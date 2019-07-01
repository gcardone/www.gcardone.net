---
layout: post
title:  "Confidence interval"
date:   2018-12-01
excerpt: About confidence intervals. What's their intuitive meaning, what they really are, and how to calculate them.
---

## What is the Confidence Interval

According to the [Statistics Glossary v1.1](http://www.stats.gla.ac.uk/steps/glossary/confidence_intervals.html) by Valerie J. Easton & John H. McColl:

> A *confidence interval* gives an estimated range of values which is likely to include an unknown population parameter, the estimated range being calculated from a given set of sample data

The “unknown population parameter” is usually the population mean, so in the following I will just assume that the “unknown population parameter” is indeed the mean.

For example, let's say you want to measure the average height of 30 year old Italian men[^1]. You randomly select 50 Italian men that fit your criteria, and plot their heights on a histogram. If you selected your sample fairly (i.e.: every candidate had an equal chance of being selected) then your histogram could looks something like this:

![An histogram with 50 samples](/assets/img/random_normal_sample_1.svg)

The mean is 177.85cm, and the distribution is somewhat bell-shaped, as expected. However, there's nothing special about your selection process. If you run the same experiment the next day, you might get something like this:

![Another histogram with 50 samples](/assets/img/random_normal_sample_2.svg)

This time the mean is 174.06cm. These averages are different, and they are not the *actual* average that you could get if you measured the height of all 30 year old Italian men. However, they are close to the actual average. At this point you can probably guess that actual average height of 30 year old Italian men is probably between 170cm and 180cm[^2].

The key observation is that every time you sample the population you will getter a different mean, and that mean will get closer to the actual mean the bigger the size of your sample is. If you measured the height of all men except one, you would get a mean very close to the real one, but slightly different to the one you'd get if you excluded a men with a different height.

The plot below shows 10 different measurement trials: when they have few samples their averages can be even very different, but as the number of samples increases, they converge to the real average.

![Different samples converging to the same mean](/assets/img/multiple_trials.svg)

The confidence interval formalizes this concept.

A confidence interval is the proportion of possible confidence intervals that contain the true value of their corresponding parameter. If you were to repeat the experiment above from scratch, you would get a slightly different result each time, however X% of the means would fall within the X% confidence interval. An equivalent way of stating this, is that if the measuring procedure was repeated many times, and we evaluated the confidence interval each time, then the fraction of confidence intervals that contain the true mean would tend to X%[^3].

The confidence interval is an estimate of an interval computed from statistics of observed data that *might* contain the true value of a unknown population parameter (usually the mean). If the true value of the unknown parameter lies outside the X% confidence interval, then there was a sampling event which had a 1-X% (or less) of happening by chance (astute readers may notice that this is similar to p values -- that's because the two concepts [are effectively related](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC2689604/)).

Effectively the confidence interval is a measure of how surprised you should be if the real value of your population parameter happens to be outside the confidence interval itself. Outside of the 90% confidence interval? *No big deal, it happens*. Outside of the 99.999% confidence interval? *Wow, that's unlikely!*

## What the Confidence Interval *is not*

Confidence interval **is not** the probability that the population parameter lies within the interval[^4], **it is not** the interval that covers %X of the samples. And, to be clear, the confidence interval is not even guaranteed to contain the true mean at all! If this sounds hard to understand it's because *it is hard*, don't feel bad about it. Even professional scientists routinely [misinterpret confidence intervals](https://en.wikipedia.org/wiki/Confidence_interval#Meaning_and_interpretation). This includes statistics students[^5] and doctors[^6].

## Evaluating the Confidence Interval in Python

In general the confidence interval depends on what are the distribution of the population and the population parameter that you are interested in. And even in that case, there may be several confidence intervals. For example [Comparison of confidence intervals for the Poisson mean: some new aspects](https://scholar.google.co.uk/scholar?hl=en&as_sdt=0%2C5&q=Comparison+of+confidence+intervals+for+the+Poisson+mean%3A+some+new+aspects&btnG=) by VV Patil and HV Kulkami lists 19 different confidence intervals for the mean of a Poisson distribution, with slightly different properties.

However, a fairly common case is calculating the confidence interval for the mean of a population with normal distribution. In this case, with unknown mean $$\mu$$, unknown standard deviation $$\sigma$$, a confidence interval for the population mean, based on a random sample size, is $$\bar{x} \pm t^\ast \frac{s}{\sqrt{n}}$$, where:

- $$\bar{x}$$ is the *sample mean*;
- $$n$$ is the *sample size*;
- $$s$$ is the *sample standard deviation*;
- $$C$$ is the *confidence interval*, which must be $$0 \leq C \leq 1$$;
- $$t^\ast$$ is the upper $$\dfrac{1-C}{2}$$ *critical value* for the Student's t-distribution with $$n-1$$ degrees of freedom (see [NIST Engineering Statistics Handbook](https://www.itl.nist.gov/div898/handbook/eda/section3/eda362.htm) about Inverse Survival Function);

Different distributions will have different confidence intervals.

Implementing confidence interval is straightforward from the definition above using [NumPy](https://www.numpy.org) and [SciPy](https://www.scipy.org):

```python
# -*- coding: utf-8 -*-

import numpy as np
from scipy import stats

def ConfidenceInterval(values, ci=0.95):
  '''Calculate confidence interval of a list of numbers using T distribution.

  Args:
    values: a valid parameter for a numpy array construction.
    ci: confidence interval, must be 0 ≤ ci ≤ 1.
  Returns:
    (lower_bound, upper_bound) tuple.
  '''
  x = np.array(values)
  n = len(x)                           # Number of samples
  x_hat = x.mean()                     # Sample mean
  s = x.std()                          # Sample standard variation
  t_star = stats.t.isf((1-ci)/2, n-1)  # Critical value
  margin = t_star * s / np.sqrt(n)
  lb = x_hat - margin                  # Confidence interval lower bound
  ub = x_hat + margin                  # Confidence interval upper bound
  return lb, ub
```

As your sample set increases the lower and upper bound will get tighter on the mean. Moreover, with a lower confidence interval the two bounds get tighter - intuitively this make sense, because the confidence interval will target fewer experiments that need to get close to the mean measured by the current experiment.

The image below shows the 99% and 90% confidence intervals calculated over a set whose size increases from 2 to 2000 samples:

![90% and 99% confidence intervals](/assets/img/confidence_interval_increasing_samples.svg)

There are three things to note in this plot:

1. The 90% confidence interval is much tighter than the 99% one. This is because the 90% confidence interval is less strict: there can be 10% of confidence intervals from other sampling experiments that can be farther away.
1. The confidence interval bounds get closer to each other as the number of samples increases.
1. Note how towards 90 samples or so, the 90% and 99% confidence intervals _do not_ include the real average of 177.1cm. Although unlikely, this is far from an impossible event.

## Conclusion

This article presented confidence intervals: what it intuitively is, and how to calculate it for a normal distribution in Python. Confidence intervals are an useful tool to gauge how confident you can be about a population parameter estimated from sampling. Whenever you see a plot or a table with averages, you should ask to see the confidence intervals as well -- if available. They will make it much easier for you to estimate how surprised you should be if the actual average turns out being different from the measured one.

### Footnotes
[^1]: Measuring population height is a classic example of a normal distribution. But in the real world is a deceptively complicated task. Self-reported height is systematically misreported, and height depends on genetic and environmental factors. For an example of analysis of population height see Garcia, J., & Quintana-Domeque, C. (2007): [The evolution of adult height in Europe: a brief note](https://repositori.upf.edu/bitstream/handle/10230/482/1002.pdf).
[^2]: It turns out that according to the study above by Garcia and Quintana-Domeque, the average height for Italian men born between 1976 and 1980 was 177.1cm with a standard deviation of 6.5cm.
[^3]: Cox D.R., Hinkley D.V. (1974). [Theoretical Statistics](https://doi.org/10.1201/b14832), Chapman & Hall, p49, p209
[^4]: R. D. Morey, R. Hoekstra, J. N. Rouder, M. D. Lee, E.-J. Wagenmakers (2016). [The Fallacy of Placing Confidence in Confidence Intervals](http://doi.org/10.3758/s13423-015-0947-8).
[^5]: W. Krämer, G. Gigerenzer (2005). How to Confuse with Statistics or: The Use and Misuse of Conditional Probabilities. *Statistical Science*.
[^6]: R. Bramwell, H. West (2006). Health professionals' and service users' interpretation of screening test results: experimental study. *BMJ*.
