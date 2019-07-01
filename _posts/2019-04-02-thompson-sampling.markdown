---
layout: post
title:  Multi-armed bandit and Thompson Sampling in C++ and Python
date:   2019-04-02
excerpt: >
  "Multi-armed bandit" is a statistical problem where given several slot machines (sometimes known as "one armed bandits") with unknown payouts, a gambler has to decide on which machines to play, in which order, and how many times to maximize the payout.
---

"Multi-armed bandit" (MAB) is a statistical problem where given several slot machines (sometimes known as "one armed bandits", because they "rob" the player) with unknown payouts, a gambler has to decide on which machines to play, in which order, and how many times to maximize the payout.

![A slot machine](/assets/img/slot_machine.jpg)
*A slot machine. Photo by [Hello I'm Nik](https://unsplash.com/photos/NYpOl-PJDkM?utm_source=unsplash&utm_medium=referral&utm_content=creditCopyText) on [Unsplash](https://unsplash.com/search/photos/slot-machine?utm_source=unsplash&utm_medium=referral&utm_content=creditCopyText)*

This problem requires a trade-off between exploring options (what if there is a slot machine that I haven't tried that allows me to win every single time?) and exploiting the machine that has the highest expected payoff. There isn't a unique solution to this problem, and in fact there are many different strategies, that usually alternate an **explorative stage** -- looking for the machine with the highest payout -- to an **exploitative stage** -- gambling on the machine that we believe provides the best rewards.

Far from being abstract, MAB model can be applied to problems where an agent simultaneously attempts to gather new information while maximizing the value over a period of time. Some examples of such problems are:

* clinical trials of different treatments while minimizing patient losses;
* optimizing design of commercial web pages to maximize the number of transactions;
* optimizing a route exploring different paths;
* goods pricing;
* watch list recommendations.

In the following I will assume a variant of MAB problem also known as *Bernoulli Bandit*: there are $$K$$ bandits, and when played each machine will result in success or a failure. Each bandit will result in success with probability $$0 \leq p_k \leq 1$$. The success probability are unknown, but they do not change over time, so they can be learned by gambling on each machine.

Thompson sampling
-----------------

There are [many different strategies](https://www.cs.mcgill.ca/~vkules/bandits.pdf) for MAB, with different guarantees, convergence speed, and statistical significance. In this article I focus on a particularly elegant solution called *Thompson sampling*.

Thompson sampling was invented in 1933 by William R. Thompson[^1]. In his paper "On the likelihood that one unknown probability exceeds another in view of the evidence of two samples", Thompson addressed the question of how to efficiently administer an experimental cure and minimize patient losses. Since then it has seen a new "golden era" thanks to research showing that it has very good performances in real-world scenarios[^2][^3].

Thompson sampling works by associating each bandit to a model distribution based on the outcomes observed so far (this is called *prior*, because it's an estimate before we decide to take an action[^4]), and choosing on which machine to bet based on samples from those model distributions. Finally, we update the model distributions based on the outcome of the machine that we chose.

Slightly more formally:

```
# for each betting round:
for i = 1, 2, … do
  
  # for each k-th bandit:
  for k = 1, 2, …, K do
    alpha_k = number of wins so far on the k-th bandit
    beta_k = number of losses so far on the k-th bandit
    t_k = random sample from beta distribution(alpha_k, beta_k)
  end

  # Chose the bandit having the highest t_k
  chosen_bandit = argmax(t_k)

  x = pull the arm of the chosen bandit

  # update alpha_k and beta_k of the chosen bandit
end
```

That's it. Really, the implementation is not hard at all.

The key point of Thompson sampling is that instead of simply choosing the bandit with the highest wins/trials ratio, we instead sample a random variable from a beta distribution. This allows Thompson sampling to explore bandits that would be ignored by a greedy strategy that simply selects the most favourable bandit so far.

A good question is: why using beta distribution? This is outside the scope of this blog post, for an in-depth discussion I suggest [A tutorial on Thompson Sampling](https://web.stanford.edu/~bvr/pubs/TS_Tutorial.pdf)[^5]. For this blog post, it's sufficient to say that beta distribution is a common tool to analyze the distribution of distributions: it's "smart" enough to model the fact that if you toss a coin once and you get tails, it does not necessarily mean that you will get tails forever, but if you toss it 1000 times and you always get tails then yes, you will probably get tails forever. I recommend reading David Robinson's [Understanding the beta distribution (using baseball statistics)](http://varianceexplained.org/statistics/beta_distribution_and_baseball/) to learn more about the beta distribution.

Python implementation
---------------------

With [numpy](https://www.numpy.org) and [scipy](https://www.scipy.org) it's easy to translate the pseudo-code above into an actual working implementation:

```python
import numpy as np
import scipy
import scipy.stats as stats

# Seed the random generator with a constant for the sake of deterministic
# results
np.random.seed(42)

# Number of times we are going to bet on the bandits
NUM_BETS = 1000
# Probability of winning for each bandit. Change this variable to experiment
# with different probabilities of winning.
p = [0.25, 0.45, 0.55]
num_bandits = len(p)
# Number of wins per bandit
wins = [0]*num_bandits
# Number of losses per bandit
losses = [0]*num_bandits

# Initialize prior distributions for each bandit with beta(alpha=1, beta=1)
prior_distributions = [scipy.stats.beta(a=1, b=1) for _ in range(num_bandits)]

for _ in range(NUM_BETS):
    # Sample a random value from each prior distribution
    theta_samples = [float(dist.rvs(1)) for dist in prior_distributions]

    # Select the bandit that has the highest sampled value from the prior
    # distributions
    chosen_bandit = np.argmax(theta_samples)
    
    # Pull the bandit's lever and observe a win or a loss
    if np.random.rand() < p[chosen_bandit]:
        wins[chosen_bandit] = wins[chosen_bandit] + 1
    else:
        losses[chosen_bandit] = losses[chosen_bandit] + 1

    # Update the beta distribution of the chosen bandit
    alpha = 1 + wins[chosen_bandit]
    beta = 1 + losses[chosen_bandit]
    prior_distributions[chosen_bandit] = scipy.stats.beta(a=alpha, b=beta)

for k in range(num_bandits):
    estimated = float(wins[k])/(wins[k] + losses[k])
    print('Bandit %d: wins/trials: %d/%d. Estimated p: %.3f. Actual p: %.3f' % (
            k+1, wins[k], wins[k]+losses[k],estimated, p[k]))

print('')
print('Expected number of wins with optimal strategy: %.3f' % (max(p) * NUM_BETS))
print('Actual wins: %d' % sum(wins))
```

The output will be:

```
Bandit 1: wins/trials: 3/13. Estimated p: 0.231. Actual p: 0.250
Bandit 2: wins/trials: 22/57. Estimated p: 0.386. Actual p: 0.450
Bandit 3: wins/trials: 539/930. Estimated p: 0.580. Actual p: 0.550

Expected number of wins with optimal strategy: 550.000
Actual wins: 564
```

Note how Thompson sampling "wasted" very few trials on the bandits with lower payouts (exploration) and spent most of the bets on the bandit with the highest payout (exploitation). If the payout of bandits is very similar, it may take a long time for the algorithm to converge on it.

C++ implementation
------------------

The C++ implementation of the same algorithm is surprisingly compact and close to the Python implementation, as long as we allow ourselves to use modern C++ constructs and the [Boost random library](https://www.boost.org/doc/libs/1_69_0/doc/html/boost_random.html).

```cpp
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <iterator>
#include <vector>
#include <boost/random.hpp>
#include <boost/random/discrete_distribution.hpp>
#include <boost/random/mersenne_twister.hpp>

// Define base_generator as a Mersenne Twister. This is needed only to make the
// code a bit less verbose.
typedef boost::mt19937 base_generator;


// pull_lever has a chance of 1/weight of returning 1.
unsigned int pull_lever(base_generator *gen, double weight) {
  double probabilities[] = {1-weight, weight};
  boost::random::discrete_distribution<> dist(probabilities);
  return dist(*gen);
}

// argmax returns the index of maximum element in vector v.
template<class T>
size_t argmax(const std::vector<T>& v){
  return std::distance(v.begin(), std::max_element(v.begin(), v.end()));
}


int main(int argc, char* argv[]) {
  unsigned int runs = 0;
  // Probability of winning for each bandit. Change this variable to experiment
  // with different probabilities of winning.
  std::vector<double> p{0.25, 0.45, 0.55};

  // Number of trials per bandit
  auto trials = std::vector<unsigned int>(p.size());
  // Number of wins per bandif
  auto wins = std::vector<unsigned int>(p.size());
  // Beta distributions of the priors for each bandit
  std::vector<boost::random::beta_distribution<> > prior_dists;
  // Initialize the prior distributions with alpha=1 beta=1
  for (size_t i = 0; i < p.size(); i++) {
    prior_dists.push_back(boost::random::beta_distribution<>(1, 1));
  }
  // gen is a Mersenne Twister random generator. We initialzie it here to keep
  // the binary deterministic.
  base_generator gen;
  for (unsigned int i = 0; i < runs; i++) {
    std::vector<double> priors;
    // Sample a random value from each prior distribution.
    for (auto& dist : prior_dists) {
      priors.push_back(dist(gen));
    }
    // Select the bandit that has the highest sampled value from the prior
    size_t chosen_bandit = argmax(priors);
    trials[chosen_bandit]++;
    // Pull the lever of the chosen bandit
    wins[chosen_bandit] += pull_lever(&gen, p[chosen_bandit]);

    // Update the prior distribution of the chosen bandit
    auto alpha = 1 + wins[chosen_bandit];
    auto beta = 1 + trials[chosen_bandit] - wins[chosen_bandit];
    prior_dists[chosen_bandit] = boost::random::beta_distribution<>(alpha, beta);
  }

  auto sp = std::cout.precision();
  std::cout << std::setprecision(3);
  for (size_t i = 0; i < p.size(); i++) {
    std::cout << "Bandit " << i+1 << ": ";
    double empirical_p = double(wins[i]) / trials[i];
    std::cout << "wins/trials: " << wins[i] << "/" << trials[i] << ". ";
    std::cout << "Estimated p: " << empirical_p << " ";
    std::cout << "Actual p: " << p[i] << std::endl;
  }
  std::cout << std::endl;
  auto expected_optimal_wins = *std::max_element(p.begin(), p.end()) * runs;
  std::cout << std::setprecision(sp);
  std::cout << "Expected number of wins with optimal strategy: " << expected_optimal_wins << std::endl;
  std::cout << "Actual wins: " << std::accumulate(wins.begin(), wins.end(), 0) << std::endl;

  return(0);
}
```

The output of this binary is similar to the previous one:

```
Bandit 1: wins/trials: 1/10. Estimated p: 0.1 Actual p: 0.25
Bandit 2: wins/trials: 49/107. Estimated p: 0.458 Actual p: 0.45
Bandit 3: wins/trials: 491/883. Estimated p: 0.556 Actual p: 0.55

Expected number of wins with optimal strategy: 550
Actual wins: 541
```

Conclusion
----------

Implementing Thompson Sampling in Python and C++ is straightforward, if we are allowed to use modern libraries, and it's a very interesting exercise. Keep in mind though that Thompson Sampling is not a silver bullet for all problems that require a trade off between the cost of exploration and the reward of exploitation. In particular Thompson Sampling requires more iterations to converge on a statistically significant outcome compared to other techniques (e.g., A/B testing), but on the other hand it minimizes losses. Whether it's the best tool for a specific problem depends on the constraints that need to be satisfied.

References
----------
[^1]: Thompson, William R. "On the likelihood that one unknown probability exceeds another in view of the evidence of two samples." *Biometrika* 25.3/4 (1933): 285-294 [https://www.jstor.org/stable/2332286](https://www.jstor.org/stable/2332286)
[^2]: Chapelle, Olivier; and Lihong Li. "An empirical evaluation of thompson sampling." *Advances in neural information processing systems*. 2011 [http://papers.nips.cc/paper/4321-an-empirical-evaluation-of-thompson-sampling](http://papers.nips.cc/paper/4321-an-empirical-evaluation-of-thompson-sampling)
[^3]: Scott, Steven L. “A modern Bayesian look at the multi-armed bandit”. *Applied Stochastic Models in Business and Industry*. 26(6): 639–658. 2010. [https://dl.acm.org/citation.cfm?id=1944432](https://dl.acm.org/citation.cfm?id=1944432).
[^4]: Some literature refers to the same distributions as *posteriors*, because they are based on what has been observed so far.
[^5]: Russo, Daniel J.; Van Roy, Benjamin; Kazerouni, Abbas;  Osband, Ian; and Wen, Zheng. "A Tutorial on Thompson Sampling". [https://web.stanford.edu/~bvr/pubs/TS_Tutorial.pdf](https://web.stanford.edu/~bvr/pubs/TS_Tutorial.pdf)
