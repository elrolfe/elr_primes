# Prime Number Iterator and Calculations

This library provides a structure for iterating through prime numbers
as well as methods for calculating prime factors and classifying
numbers as prime or composite.

[API Reference (docs.rs)](https://https://docs.rs/elr_primes/0.1.1)

## Using this library

Add the following to your `Cargo.toml` file

```toml
[dependencies]
elr_primes = "0.1.1"
```

## Examples

Basic Usage:

```rust
use elr_primes::Primes;

// Provides an iterator for all prime numbers less than or equal to 1000
let mut p = Primes::new(1000);
```

Once the structure has been initiated, the `primes()` method provides an iterator
for the prime numbers.

```rust
# use elr_primes::Primes;
let p = Primes::new(10);  // Primes less than or equal to 10
let mut prime_iter = p.primes();
let primes: Vec<usize> = prime_iter.copied().collect();
let expected: [usize; 4] = [2, 3, 5, 7];
assert_eq!(primes, expected);
```

Since `primes()` returns an iterator, you can also use it to directly find a specific
prime number.

```rust
# use elr_primes::Primes;
let p = Primes::new(100); // Primes less than or equal to 100
let n = 20;

// Iterators are zero-based, so to get the 20th prime we need to search for the 19th
match p.primes().nth(n - 1) {
    Some(x) => println!("The {}th prime is: {}", n, x),
    None => println!("The {}th prime is outside the current bounds", n)
};
```

Methods are also available to find the prime factors of a number, and whether a
number is prime or composite.

```rust
use elr_primes::{Primes, Primality};
let p = Primes::new(100);

let n = 96;
match p.factors(n) {
    Ok(factors) => println!("{:?}", factors),
    Err(_) => println!("Could not find all prime factors within the bounds"),
};

let n = 23;
match p.primality(n) {
    Primality::Prime => println!("{} is prime", n),
    Primality::Composite => println!("{} is composite", n),
    Primality::Unknown => println!("Primality of {} is undetermined", n),
};
```
