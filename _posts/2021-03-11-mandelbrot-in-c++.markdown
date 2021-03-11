---
layout: post
title:  "Mandelbrot rendering in C++: comparison with Rust"
date:   2021-03-11
excerpt: >
  I implemented a renderer of the Mandelbrot set in Rust. Here I compare it with the same algorithms implemented in C++.
---

* ToC
{:toc}

# In the previous episode…

In [a previous post]({% link _posts/2021-03-04-blistering-fast-mandelbrot-in-rust.markdown %}) I implemented a renderer for the [Mandelbrot set](https://en.wikipedia.org/wiki/Mandelbrot_set) in Rust. When I ran it to render a 14000 x 8000 image the running time was:

```
Executing naive... 18.437s
Executing avxrayon... 6.668s
Executing opencl... 0.816s
```

And when rendering a 56000 x 32000 image the running time was:

```
Executing naive... 314.635s
Executing avxrayon... 119.919s
Executing opencl... 9.468s
```

I was disappointed by the speedup, so I decided to implement the same algorithms in C++ for comparison.

# C++ implementation

I won't spend time explaining the algorithms here, I will just copy the C++ code. All the algorithms are pretty much perfect maps of the Rust code that I wrote in my [previous post]({% link _posts/2021-03-04-blistering-fast-mandelbrot-in-rust.markdown %}).

```cpp
// Use https://github.com/lvandeve/lodepng/ for PNG encoding.
#include "lodepng.h"

#define CL_TARGET_OPENCL_VERSION 220
#include <CL/cl.h>
#include <immintrin.h>

#include <chrono>
#include <functional>
#include <iomanip>
#include <iostream>
#include <memory>

inline unsigned char const MAX_ITERATIONS = 255;

// Generic Mandlebrot generator. The first argument is the image width, the
// second argument is the image height. The third argument is the output
// buffer: each element contains the number of iterations of a pixels. The
// pixels are serialized sequentially by row.
typedef std::function<void(unsigned int, unsigned int, unsigned char *)>
    MandelbrotGenerator;

// This implements the naive algorithm to generate the Mandelbrot set. Note
// that a clever compiler could optimize a lot of this code.
void naive(unsigned int w, unsigned int h, unsigned char *output) {
  for (unsigned int c = 0; c < w; c++) {
    float x0 = (static_cast<float>(c) / static_cast<float>(w)) * 3.5 - 2.5;
    for (unsigned int r = 0; r < h; r++) {
      float y0 = (static_cast<float>(r) / static_cast<float>(h)) * 2.0 - 1.0;
      float x = 0.0;
      float y = 0.0;
      unsigned char iteration = 0;
      while (x * x + y * y <= 4.0 && iteration < MAX_ITERATIONS) {
        float xtemp = x * x - y * y + x0;
        y = 2.0 * x * y + y0;
        x = xtemp;
        iteration++;
      }
      auto idx = (w * r + c);
      output[idx] = iteration;
    }
  }
}
```

So far, so good. The code above is the simple implementation of the naive algorithm to draw the Mandelbrot set.

The algorithm is embarrassingly parallel, so we can use [OpenMP](https://www.openmp.org) without worrying too much to parallelize it. To do so, it's sufficient to add `#pragma omp parallel for` before the loop to parallelize, and pass `-fopenmp` to `g++`:

```cpp

// Same as above, but ask OpenMP to parallelize the external loop. Effort-wise
// this is close to using Rayon in Rust.
void openmp(unsigned int w, unsigned int h, unsigned char *output) {
// Use OpenMP to parallelize the loop. Let OpenMP decide on the number of
// threads to use.
#pragma omp parallel for
  for (unsigned int c = 0; c < w; c++) {
    float x0 = (static_cast<float>(c) / static_cast<float>(w)) * 3.5 - 2.5;
    for (unsigned int r = 0; r < h; r++) {
      float y0 = (static_cast<float>(r) / static_cast<float>(h)) * 2.0 - 1.0;
      float x = 0.0;
      float y = 0.0;
      unsigned char iteration = 0;
      while (x * x + y * y <= 4.0 && iteration < MAX_ITERATIONS) {
        float xtemp = x * x - y * y + x0;
        y = 2.0 * x * y + y0;
        x = xtemp;
        iteration++;
      }
      auto idx = (w * r + c);
      output[idx] = iteration;
    }
  }
}
```

The next step is to use AVX2 registers and intrinsics. This is very similar to the code I used for Rust:

```cpp
// Let's roll up our sleeves and implement the algorithm using AVX2 intrinsics.
// Luckily this is almost a 1:1 copy of the Rust code.
void avx2(unsigned int w, unsigned int h, unsigned char *output) {
#pragma omp parallel for
  for (unsigned int c = 0; c < w; c++) {
    float x0 = (static_cast<float>(c) / static_cast<float>(w)) * 3.5 - 2.5;
    // Initialize ax0 as 8 packed single precision float initialized to x0.
    auto ax0 = _mm256_set1_ps(x0);
    // r is the row to process, that is the y coordinate. We step by 8
    // because AVX2 packs 8 floats in a single register.
    for (unsigned int r = 0; r < h; r += 8) {
      // Initialize a temporary variable with r, repeated 8 times, and
      // then add 7, 6, ... 0 to the ar coordinates. This means that the
      // floats packed in ay0 contain the coordinates of contiguous
      // pixels along the y axis.
      auto ay0 =
          _mm256_add_ps(_mm256_set_ps(7.0, 6.0, 5.0, 4.0, 3.0, 2.0, 1.0, 0.0),
                        _mm256_set1_ps(static_cast<float>(r)));
      // ay0 = (r / h) * 2 - 1
      ay0 = _mm256_sub_ps(
          _mm256_mul_ps(
              _mm256_div_ps(ay0, _mm256_set1_ps(static_cast<float>(h))),
              _mm256_set1_ps(2.0)),
          _mm256_set1_ps(1.0));
      // ax = 0
      auto ax = _mm256_set1_ps(0.0);
      // ay = 0
      auto ay = _mm256_set1_ps(0.0);
      // aiters contains the number of iterations for each pixel,
      // initializeda to 0.
      auto aiters = _mm256_set1_epi32(0);
      // If a packed integer in amask is set to 1, then the iterator in
      // aiters in the same position will be incremented. This allows us
      // to repeat the core escape loop only if at least one of the pixels
      // needs more iterations.  If amask is all set to zero then we can
      // bail out.
      auto amask = _mm256_set1_epi32(1);
      for (unsigned char it = 0; it < MAX_ITERATIONS; it++) {
        // axsq = x * x
        auto axsq = _mm256_mul_ps(ax, ax);
        // aysq = y * y
        auto aysq = _mm256_mul_ps(ay, ay);
        // axtemp = x * x - y * y + x0
        auto axtemp = _mm256_add_ps(_mm256_sub_ps(axsq, aysq), ax0);
        // y = 2.0 * x * y + y0
        // The "2.0 * x" multiplication has been replaced with a more
        // efficient x + x
        ay = _mm256_add_ps(_mm256_mul_ps(_mm256_add_ps(ax, ax), ay), ay0);
        ax = axtemp;
        // Increase all the iterations if the matching mask is set to 1.
        aiters = _mm256_add_epi32(aiters, amask);
        // threshold = x * x + y * y
        auto athreshold = _mm256_add_ps(axsq, aysq);
        // Compare the values in athreshold with 4.0, and store 0xFFFFFFFF in
        // acond if the condition is true, 0 otherwise.
        auto acond = _mm256_cmp_ps(athreshold, _mm256_set1_ps(4.0), _CMP_LE_OQ);
        // Do a logical and between amask and the acond. This means that each
        // packed integer in amask will be set to zero iff x * x + y * y > 4.0.
        amask = _mm256_and_si256(amask, _mm256_castps_si256(acond));
        // If amask contains only bits set to zero, then we don't need to keep
        // iterating.
        if (_mm256_testz_si256(amask, _mm256_set1_epi32(-1))) {
          break;
        }
        // Unpack the iteration values in a old-fashioned array
        int iters[8];
        _mm256_maskstore_epi32(iters, _mm256_set1_epi32(-1), aiters);
        for (int i = 0; i < 8; i++) {
          auto idx = w * (r + i) + c;
          output[idx] = static_cast<unsigned char>(iters[i]);
        }
      }
    }
  }
}
```

And finally: OpenCL. OpenCL API is designed for C, so it's not the most pleasant thing to use in C++:

```cpp
// Version using OpenCl.
void opencl(unsigned int w, unsigned int h, unsigned char *output) {
  cl_command_queue command_queue;
  cl_context context;
  cl_device_id device;
  cl_kernel kernel;
  cl_mem buffer;
  cl_platform_id platform;
  cl_program program;
  // work_dim is the size of the 2-dimensional data structure that OpenCL
  // workers will use.
  size_t work_dim[2] = {w, h};
  size_t buf_size = static_cast<size_t>(w) * static_cast<size_t>(h);
  // clang-format off
  // This is the code of an OpenCL kernel. An OpenCL kernel is the code that
  // runs on an device. Note that this is technically a one-liner because
  // There are no "\n". Rust makes this less error-prone because it natively
  // supports multi-line string constants.
  const char *src =
    "kernel void mandelbrot(__global uchar* buffer, uint width, uint height,"
    "                       uchar max_iterations) {"
    "  /*"
    "   * Get the x coordinate of this worker. We can get x and y coordinates "
    "   * because the kernel operates over a 2-dimensional data structure."
    "   */"
    "  int c = get_global_id(0);"
    "  /* Get the y coordinate of this worker. */"
    "  int r = get_global_id(1);"
    "  /*"
    "   * The code below is an almost line-by-line port of the naive"
    "   * implementation, which has been optimized to have only 3"
    "   * multiplications in the inner loop."
    "   */"
    "  float x0 = ((float)c / width) * 3.5 - 2.5;"
    "  float y0 = ((float)r / height) * 2.0 - 1.0;"
    "  float x = 0.0;"
    "  float y = 0.0;"
    "  float x2 = 0.0;"
    "  float y2 = 0.0;"
    "  uchar iteration = 0;"
    "  while (((x2 + y2) <= 4.0) && (iteration < max_iterations)) {"
    "      y = (x + x) * y + y0;"
    "      x = x2 - y2 + x0;"
    "      x2 = x * x;"
    "      y2 = y * y;"
    "      iteration = iteration + 1;"
    "  }"
    "  /* Store the number of iterations computed by this worker. */"
    "  buffer[width * r + c] = iteration;"
    "}";
  // clang-format on

  // NOTE: the code below does not do any error handling to avoid clutter.
  // Real world code should check for errors.

  // Retrieve one platform that supports OpenCL. A platform is a host and a
  // collection of devices that support OpenCL.
  clGetPlatformIDs(1, &platform, NULL);
  // Retrieve a device. In general a platform can have multiple devices, but
  // this code assumes that there's only one OpenCL-aware GPU.
  clGetDeviceIDs(platform, CL_DEVICE_TYPE_GPU, 1, &device, NULL);
  // Create an OpenCL context, which is the environment where a kernel
  // executes. Here we are creating a context associated to just one device.
  context = clCreateContext(NULL, 1, &device, NULL, NULL, NULL);
  // A command queue is a container of commands that should be executed on a
  // device.
  command_queue =
      clCreateCommandQueueWithProperties(context, device, NULL, NULL);
  // A buffer is a memory area that can be accessed by all OpenCL workers.
  // This is where each worker will write its output.
  buffer = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_ALLOC_HOST_PTR,
                          buf_size, NULL, NULL);
  // A program is a collection of kernels.
  program = clCreateProgramWithSource(context, 1, &src, NULL, NULL);
  // Compile the OpenCL program.
  clBuildProgram(program, 1, &device, "", NULL, NULL);
  // Create a kernel object and pass arguments to it.
  kernel = clCreateKernel(program, "mandelbrot", NULL);
  clSetKernelArg(kernel, 0, sizeof(cl_mem), &buffer);
  clSetKernelArg(kernel, 1, sizeof(cl_uint), &w);
  clSetKernelArg(kernel, 2, sizeof(cl_uint), &h);
  clSetKernelArg(kernel, 3, sizeof(cl_uchar), &MAX_ITERATIONS);
  // Enqueue a task in the command queue that will run the kernel over a 2-
  // dimensional data structure (work_dim) of dimension w x h.
  clEnqueueNDRangeKernel(command_queue, kernel, 2, NULL, work_dim, NULL, 0,
                         NULL, NULL);
  // Flush all the commands in the command queue.
  clFlush(command_queue);
  // Wait until all commands in the queue are completed.
  clFinish(command_queue);
  // Copy the results stored in buffer to output.
  clEnqueueReadBuffer(command_queue, buffer, CL_TRUE, 0, buf_size, output, 0,
                      NULL, NULL);
}
```

The last bit is a simple function that runs a Mandelbrot generator function and optionally saves its output to a PNG file. I decided to use https://github.com/lvandeve/lodepng/ to write the PNG file. I tried https://github.com/nothings/stb/ too, which seems to be more popular, but it didn't work for larger PNG files.

Anyway, here's the code:

```cpp
// Run a Mandelbrot generator algorithm, report its running time, and
// optionally save its output to a PNG file.
void runalgo(const char *name, unsigned int width, unsigned int height,
             MandelbrotGenerator gen, bool savepng) {
  // Size of the output buffer.
  size_t output_size = static_cast<size_t>(width) * static_cast<size_t>(height);
  // Use unique_ptr to free memory at the end of this function.
  std::unique_ptr<unsigned char[]> output(new unsigned char[output_size]);
  // This is not a robust way to generate file paths.
  std::string filename = std::string{"/tmp/mandelbrot_"} + name + ".png";
  std::cout << "Running " << name << "... " << std::flush;
  auto start = std::chrono::high_resolution_clock::now();
  gen(width, height, output.get());
  auto end = std::chrono::high_resolution_clock::now();
  auto duration =
      std::chrono::duration_cast<std::chrono::milliseconds>(end - start)
          .count() /
      1000.0;
  // I wish I could use libfmt or the new <format> header without having to
  // manually compile GCC from trunk or something like that.
  std::cout << std::fixed << std::setprecision(3) << duration << "s"
            << "\n";
  if (savepng) {
    unsigned int error = lodepng::encode(filename.c_str(), output.get(), width,
                                         height, LCT_GREY);
    if (error) {
      std::cout << "PNG encoder error: " << lodepng_error_text(error) << "\n";
    }
  }
}

int main() {
  constexpr int width = 14000;
  constexpr int height = 8000;
  constexpr bool savepng = true;
  runalgo("naive", width, height, naive, savepng);
  runalgo("openmp", width, height, openmp, savepng);
  runalgo("avx2", width, height, avx2, savepng);
  runalgo("opencl", width, height, opencl, savepng);
  return 0;
}
```

Now that we have everything ready we can compile and run it:

```
$ g++ -Wall -pedantic -std=c++17 -fopenmp -mavx2 -O3 lodepng.cpp mandelbrot.cpp -lOpenCL && ./a.out
Running naive... 27.262s
Running openmp... 7.513s
Running avx2... 0.738s
Running opencl... 0.207s
```

And with a larger image:

```
// constexpr int width = 56000;
// constexpr int height = 32000;
Running naive... 950.421s
Running openmp... 257.737s
Running avx2... 102.910s
Running opencl... 0.935s
```

So, to summarize:


C++:

Algorithm    | 14000 x 8000   | 56000 x 32000
-------------|----------------|---------------
Naive        | 27.262 (1x)    | 950.421 (1x)
OpenMP       | 7.513 (3.6x)   | 257.737 (3.6x)
AVX2         | 0.738 (36.9x)  | 102.910 (4.9x)
OpenCL       | 0.207 (131.7x) | 0.935 (1016x)


Rust:

Algorithm    | 14000 x 8000 | 56000 x 32000
-------------|--------------|--------------
Naive        | 18.437s (1x) | 314.635 (1x)
AVX2 + Rayon | 6.668 (2.7x) | 119.919 (2.6x)
OpenCL       | 0.816 (22x)  | 9.468 (33.2x)

A few observations:

- The naive algorithm is between 1.4x and 3x faster in Rust than C++
- The OpenCL implementation is _massively_ more performant in C++
- C++ performances vary wildly, the decrease in performance of AVX2 suggest that, well, I should run every algorithm several times ;)

So, things to do in a follow up post:

- compare the generated assembly to understand why optimized C++ is faster than Rust
- run the algos several times because seriously, don't trust benchmarks of a function that has been ran exactly once :)
