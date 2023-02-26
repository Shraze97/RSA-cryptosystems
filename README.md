# RSA-cryptosystems
Here we will use the following resources :-
https://drive.google.com/drive/folders/1-hugfGRaFiWQaxi7eQS9a4WY8hQN23Oo?usp=share_link

The RSA, named after its inventors Rivest, Shamir, and Adleman [RSA78], is a popular public-key cryptosystem. A cryptosystem is an encryption-cum-decryption scheme for communication between a sender and a receiver. Such a system is secure if it is  infeasible for a (potentially malicious) third party to eavesdrop
on the encrypted message and decrypt it efficiently. In a public-key cryptosystem, the receiver publishes a common key (also known as the public key) using which anyone can encrypt a message and send it to the receiver. On the other hand, only the receiver knows a secret private key using which the message can be
decrypted efficiently. 

The RSA key generation procedure is as follows.
ALGORITHM 1: RSA: Key Generation
1. Fix a key length, say, $2^r$ bits.
2. Randomly select two distinct primes $p$ and $q$ each of $2^{r-1} bits.
3. Let $n = pq$ and $\phi(n) = (p-1)(q-1)$, the totient function.
4. Randomly select an $e$ such that $3\le e\le \phi(n)$ and $gcd(3,\phi(n))=1$.
5. Find the smallest $d$ such that $d \times e = 1 mod \phi(n)$.
6. The encryption key is the pair $(n, e)$.
7. The decryption key is $d$.

The public key consists of the modulus $n$ and the public (or encryption) exponent $e$. The private key consists of the private (or decryption) exponent $d$, which is kept secret. $p$, $q$, and $\phi(n)$ are also kept secret as they can be used to calculate $d$.

