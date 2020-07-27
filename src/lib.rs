#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]
//! # Prime Number Iterator and Calculations
//!
//! This library provides a structure for iterating through prime numbers
//! as well as methods for calculating prime factors and classifying
//! numbers as prime or composite.
//! # Using this library
//!
//! Add the following to your `Cargo.toml` file
//! ```toml
//! [dependencies]
//! elr_primes = "0.1.0"
//! ```
//!
//! # Examples
//!
//! Basic Usage:
//! ```rust
//! use elr_primes::Primes;
//!
//! // Provides an iterator for all prime numbers less than or equal to 1000
//! let mut p = Primes::new(1000);
//! ```
//!
//! Once the structure has been initiated, the `primes()` method provides an iterator
//! for the prime numbers.
//!
//! ```rust
//! # use elr_primes::Primes;
//! let p = Primes::new(10);  // Primes less than or equal to 10
//! let mut prime_iter = p.primes();
//! let primes: Vec<usize> = prime_iter.copied().collect();
//! let expected: [usize; 4] = [2, 3, 5, 7];
//! assert_eq!(primes, expected);
//! ```
//!
//! Since `primes()` returns an iterator, you can also use it to directly find a specific
//! prime number.
//!
//! ```rust
//! # use elr_primes::Primes;
//! let p = Primes::new(100); // Primes less than or equal to 100
//! let n = 20;
//!
//! // Iterators are zero-based, so to get the 20th prime we need to search for the 19th
//! match p.primes().nth(n - 1) {
//!     Some(x) => println!("The {}th prime is: {}", n, x),
//!     None => println!("The {}th prime is outside the current bounds", n)
//! };
//! ```
//!
//! Methods are also available to find the prime factors of a number, and whether a
//! number is prime or composite.
//!
//! ```rust
//! use elr_primes::{Primes, Primality};
//! let p = Primes::new(100);
//!
//! let n = 96;
//! match p.factors(n) {
//!     Ok(factors) => println!("{:?}", factors),
//!     Err(_) => println!("Could not find all prime factors within the bounds"),
//! };
//!
//! let n = 23;
//! match p.primality(n) {
//!     Primality::Prime => println!("{} is prime", n),
//!     Primality::Composite => println!("{} is composite", n),
//!     Primality::Unknown => println!("Primality of {} is undetermined", n),
//! };
//! ```
use std::slice::Iter;
use std::sync::mpsc;
use std::thread;

/// Vector of prime factor tuples.
///
/// Factors are stored as a tuple, with the first entry being the prime value
/// and the second entry being the exponent to raise the value to.
///
/// # Example
/// ```rust
/// use elr_primes::Factors;
///
/// let factors_of_18: Factors = vec![(2, 1), (3, 2)]; // 2^1 * 3^2 = 18
/// ```
pub type Factors = Vec<(usize, usize)>;

/// Primality types for numbers.
#[derive(Debug, PartialEq, Eq)]
pub enum Primality {
    /// A number is prime
    Prime,
    /// A number is composite
    Composite,
    /// A number couldn't be classified as prime or composite
    /// with the current bound of primes
    Unknown,
}

/// Prime Iterator
///
/// This provides an iterator over prime numbers up to a given maximum value.
/// The inclusive upper bound for prime numbers is provided when the structure
/// is instantiated.
///
#[derive(Debug, PartialEq, Eq)]
pub struct Primes {
    primes: Vec<usize>,
    bound: usize,
}

impl Primes {
    /// Create a new `Primes` instance.
    ///
    /// The maximum bound for prime numbers is passed as a parameter to `new()`. If the bound is
    /// less than 2, then the iterator will provide no primes.
    /// 
    /// The method spawns threads to generate blocks of threads concurrently.
    ///
    /// # Example
    ///
    /// ```rust
    /// use elr_primes::Primes;
    ///
    /// // Create an iterator for primes that are less than or equal to 1000
    /// let p = Primes::new(1000);
    /// ```
    pub fn new(bound: usize) -> Self {
        let block = 500000;
        let mut primes = vec![];
        let mut seed_primes = vec![];

        if bound > 1 {
            let root = (bound as f64).sqrt() as usize;
            let mut sieve = vec![true; root + 1];
            for i in 2..=root {
                if sieve[i] {
                    seed_primes.push(i);
                    for j in (i * i..=root).step_by(i) {
                        sieve[j] = false;
                    }
                }
            }

            let mut k = 0;

            let (tx, rx) = mpsc::channel();
            
            while k * block <= bound {
                let t_k = k;
                let t_block = block;
                let t_bound = bound;
                let t_primes = seed_primes.clone();
                let t_tx = mpsc::Sender::clone(&tx);

                thread::spawn(move || {
                    let mut sieve = vec![true; t_block];
                    let start = t_k * t_block;
                    for p in &t_primes {
                        let start_index = (start + p - 1) / p;
                        let start_index = if start_index > *p { start_index } else { *p } * *p - start;
                        for j in (start_index..t_block).step_by(*p) {
                            sieve[j] = false;
                        }
                    }

                    if t_k == 0 {
                        sieve[0] = false;
                        sieve[1] = false;
                    }

                    let result = &mut sieve.iter().enumerate().filter_map(|(v, &p)| if p && v + start <= t_bound { Some(v + start) } else { None }).collect::<Vec<usize>>();
                    t_tx.send(result.clone()).unwrap();
                });

                k += 1;
            }

            drop(tx);

            for mut received in rx {
                primes.append(&mut received);
            }
            primes.sort();
        }

        Primes { primes, bound }
    }

    /// Find the prime factors for a number.
    ///
    /// Returns a [`Factor`] type containing the factors for the number.
    ///
    /// # Errors
    ///
    /// If the the number has prime factors that are outside of the current bounds,
    /// a tuple is returned with the first element as a [`Factor`] type containing
    /// the in-bound factors found for the number, and the second element as the remainder
    /// value that could not be factored within the current bounds.
    ///
    /// [`Factor`]: type.Factors.html
    ///
    /// # Example
    ///
    /// ```rust
    /// # use elr_primes::Primes;
    /// let p = Primes::new(10);
    ///
    /// let factors = p.factors(40);
    /// assert!(factors.is_ok());
    /// assert_eq!(factors.ok(), Some(vec![(2, 3), (5, 1)])); // 2^3 * 5^1 = 40
    ///
    /// let factors = p.factors(429);
    /// assert!(factors.is_err());
    /// assert_eq!(factors.err(), Some((vec![(3, 1)], 143))); // 3^1 is a prime factor of 429
    ///                                                       // but the remainder 143 has no
    ///                                                       // factors in bounds
    /// ```
    pub fn factors(&self, value: usize) -> Result<Factors, (Factors, usize)> {
        let mut value = value;
        let mut count: usize;
        let mut result = vec![];

        for factor in &self.primes {
            count = 0;
            while value % factor == 0 {
                value /= factor;
                count += 1;
            }

            if count > 0 {
                result.push((*factor, count));
            }
        }

        if value > 1 {
            if self.primality(value) != Primality::Prime {
                return Err((result, value));
            } else {
                result.push((value, 1));
            }
        }
        Ok(result)
    }

    /// Returns the primality of a number.
    ///
    /// This method tries to determine the primality of a given number through
    /// trial division of the primes that are less than the square root of the
    /// given number.
    ///
    /// Returns:
    /// * [`Primality::Composite`] - A prime was found that is a factor of the number
    /// * [`Primality::Prime`] - No prime was found that is a factor of the number, and the
    /// square root of the number is not greater than the current bounds
    /// * [`Primality::Unknown`] - No prime was found that is a factor of the number, but the
    /// square root fo the number is greater than the current bounds
    ///
    /// [`Primality::Composite`]: enum.Primality.html
    /// [`Primality::Prime`]: enum.Primality.html
    /// [`Primality::Unknown`]: enum.Primality.html
    ///
    /// # Example
    ///
    /// ```rust
    /// use elr_primes::{Primality, Primes};
    ///
    /// let p = Primes::new(31);
    /// assert_eq!(p.primality(953), Primality::Prime);
    /// assert_eq!(p.primality(959), Primality::Composite);
    /// assert_eq!(p.primality(967), Primality::Unknown);  // 967 is prime, but it's square root
    ///                                                    // is greater than the current bound
    ///                                                    // so it cannot be definitively known
    ///                                                    // as prime through trial division
    ///
    /// assert_eq!(p.primality(969), Primality::Composite); // The square root of 969 is also
    ///                                                     // greater than the current bound, but
    ///                                                     // it has a factor (3) that is within
    ///                                                     // the bounds, so it can be classified
    ///                                                     // as a composite number
    /// ```
    pub fn primality(&self, value: usize) -> Primality {
        if value <= self.bound {
            return if self.primes.contains(&value) {
                Primality::Prime
            } else {
                Primality::Composite
            };
        }

        let root = (value as f64).sqrt();
        for prime in self.primes.iter().filter(|&x| *x as f64 <= root) {
            if value % prime == 0 {
                return Primality::Composite;
            }
        }

        if root > self.bound as f64 {
            return Primality::Unknown;
        }

        Primality::Prime
    }

    /// Returns an iterator for the bound prime numbers.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use elr_primes::Primes;
    /// let p = Primes::new(100);
    ///
    /// // Print all of the primes below 100
    /// for prime_value in p.primes() {
    ///     println!("{}", prime_value);
    /// }
    /// ```
    pub fn primes(&self) -> Iter<usize> {
        self.primes.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::{Factors, Primality, Primes};

    #[test]
    fn generates_the_first_100_primes() {
        let p = Primes::new(541); // 541 is the 100th prime, so bounding here should include it
        let primes: Vec<usize> = p.primes().copied().collect();
        assert_eq!(
            primes,
            vec![
                2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
                83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
                173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257,
                263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353,
                359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449,
                457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
            ]
        );
    }

    #[test]
    fn no_primes_below_2() {
        let p = Primes::new(0);
        let primes: Vec<usize> = p.primes().copied().collect();
        assert!(primes.is_empty());

        let p = Primes::new(1);
        let primes: Vec<usize> = p.primes().copied().collect();
        assert!(primes.is_empty());

        let p = Primes::new(2);
        let primes: Vec<usize> = p.primes().copied().collect();
        assert_eq!(primes, vec![2]);
    }

    #[test]
    fn prime_factorization() {
        let p = Primes::new(7);
        let expected: Factors = vec![(2, 1)];
        assert_eq!(expected, p.factors(2).unwrap());

        let expected: Factors = vec![(3, 1)];
        assert_eq!(expected, p.factors(3).unwrap());

        let expected: Factors = vec![(2, 2)];
        assert_eq!(expected, p.factors(4).unwrap());

        let expected: Factors = vec![(2, 3), (3, 2), (5, 1)];
        assert_eq!(expected, p.factors(360).unwrap());

        let expected: Factors = vec![(2, 1), (3, 2), (5, 3), (7, 4), (11, 1)];
        assert_eq!(expected, p.factors(59424750).unwrap());
    }

    #[test]
    fn composite_with_out_of_bound_factor() {
        let p = Primes::new(5);
        let expected: (Factors, usize) = (vec![(3, 1), (5, 1)], 29);
        assert_eq!(p.factors(435).err(), Some(expected));

        let expected: (Factors, usize) = (vec![(2, 3), (3, 2), (5, 1)], 31);
        assert_eq!(p.factors(11160).err(), Some(expected));
    }

    #[test]
    fn identifies_primes_within_bounds() {
        let p = Primes::new(2);
        assert_eq!(p.primality(2), Primality::Prime);
        assert_eq!(p.primality(4), Primality::Composite);
        assert_eq!(p.primality(5), Primality::Unknown);
        assert_eq!(p.primality(100_000_000), Primality::Composite);

        let p = Primes::new(31);
        assert_eq!(p.primality(3), Primality::Prime);
        assert_eq!(p.primality(953), Primality::Prime);
        assert_eq!(p.primality(959), Primality::Composite);
        assert_eq!(p.primality(967), Primality::Unknown);
    }
}
