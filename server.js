const express = require('express');
const path    = require('path');

const app  = express();
const PORT = process.env.PORT || 3000;

// ── Serve static files from /public ──────────────────────────────
app.use(express.static(path.join(__dirname, '.')));

// ── API: Generate Diffie-Hellman parameters server-side ──────────
app.get('/api/generate', (req, res) => {
  try {
    const p     = randomPrime(50, 200);
    const roots = primitiveRoots(p);
    const g     = roots[Math.floor(Math.random() * roots.length)];
    const a     = randomInt(2, p - 2);
    const b     = randomInt(2, p - 2);
    const A     = modPow(g, a, p);   // Alice's public value
    const B     = modPow(g, b, p);   // Bob's public value
    const K     = modPow(B, a, p);   // Shared secret  (= modPow(A,b,p))

    res.json({ p, g, a, b, A, B, K });
  } catch (err) {
    console.error('Generation error:', err);
    res.status(500).json({ error: 'Failed to generate parameters' });
  }
});

// ── Fallback: serve index.html for any unknown route ────────────
app.get('*', (req, res) => {
  res.sendFile(path.join(__dirname, 'index.html'));
});

// ── Start server ─────────────────────────────────────────────────
app.listen(PORT, () => {
  console.log(`\n Diffie-Hellman Demo running at http://localhost:${PORT}\n`);
});

// ════════════════════════════════════════════════════════════════
//  Math utilities (server-side)
// ════════════════════════════════════════════════════════════════

/** Modular exponentiation using BigInt for precision */
function modPow(base, exp, mod) {
  let b = BigInt(base);
  let e = BigInt(exp);
  let m = BigInt(mod);
  let result = 1n;
  b = b % m;
  while (e > 0n) {
    if (e % 2n === 1n) result = (result * b) % m;
    e = e >> 1n;
    b = (b * b) % m;
  }
  return Number(result);
}

/** Miller-Rabin primality test */
function isPrime(n) {
  if (n < 2) return false;
  if (n < 4) return true;
  if (n % 2 === 0) return false;
  for (let i = 3; i <= Math.sqrt(n); i += 2) {
    if (n % i === 0) return false;
  }
  return true;
}

/** Return a random prime in [min, max] */
function randomPrime(min, max) {
  const primes = [];
  for (let i = min; i <= max; i++) {
    if (isPrime(i)) primes.push(i);
  }
  if (primes.length === 0) throw new Error('No primes in range');
  return primes[Math.floor(Math.random() * primes.length)];
}

/** Return a random integer in [min, max] */
function randomInt(min, max) {
  return Math.floor(Math.random() * (max - min + 1)) + min;
}

/** Return all primitive roots (generators) of Z*_p */
function primitiveRoots(p) {
  const phi = p - 1;

  // Factorise phi
  const factors = [];
  let n = phi;
  for (let i = 2; i * i <= n; i++) {
    if (n % i === 0) {
      factors.push(i);
      while (n % i === 0) n = Math.floor(n / i);
    }
  }
  if (n > 1) factors.push(n);

  // A generator g satisfies: g^(phi/q) ≢ 1 (mod p) for every prime q | phi
  const roots = [];
  for (let g = 2; g < p; g++) {
    const isRoot = factors.every(f => modPow(g, phi / f, p) !== 1);
    if (isRoot) roots.push(g);
  }
  return roots;
}
