package de.uni_freiburg.informatik.ultimate.util;

public class HashUtils {
	public static int hashJenkins(int init, Object... vals) {
		if (vals == null || vals.length == 0) return init;
		int a,b,c;
		// TODO maybe a different value than 0xdeadbeaf???
		a = b = c = 0xcafebabe/*deadbeaf*/ + (vals.length << 2) + init;
		int pos = 0;
		while (vals.length - pos > 3) {
			a += vals[pos].hashCode();
			b += vals[pos + 1].hashCode();
			c += vals[pos + 2].hashCode();
			a -= c; a ^= ((c << 4) | (c >> 28)); c += b;
			b -= a; b ^= ((a << 6) | (c >> 26)); a += c;
			c -= b; c ^= ((b << 8) | (b >> 24)); b += a;
			a -= c; a ^= ((c << 16) | (c >> 16)); c += b;
			b -= a; b ^= ((a << 19) | (c >> 13)); a += c;
			c -= b; c ^= ((b << 4) | (b >> 28)); b += a;
			pos += 3;
		}
		switch (vals.length - pos) {
		case 3: c += vals[pos++].hashCode();
		case 2: b += vals[pos++].hashCode();
		case 1: a += vals[pos].hashCode();
			c ^= b; c -= ((b << 14) | (b >> 18));
			a ^= c; a -= ((c << 11) | (c >> 21));
			b ^= a; b -= ((a << 25) | (a >> 7));
			c ^= b; c -= ((b << 16) | (b >> 16));
			a ^= c; a -= ((c << 4) | (c >> 28));
			b ^= a; b -= ((a << 14) | (a >> 18));
			c ^= b; c -= ((b << 24) | (b >> 8));
		case 0:
		default:
			break;
		}
		return c;
	}
	
	public static int hashJenkins(int init, Object val) {
		int a,b,c;
		// TODO maybe a different value than 0xdeadbeaf???
		a = b = 0xcafebabe/*deadbeaf*/ + 4 + init;
		a += val.hashCode();
		c =  0; c -= ((b << 14) | (b >> 18));
		a ^= c; a -= ((c << 11) | (c >> 21));
		b ^= a; b -= ((a << 25) | (a >> 7));
		c ^= b; c -= ((b << 16) | (b >> 16));
		a ^= c; a -= ((c << 4) | (c >> 28));
		b ^= a; b -= ((a << 14) | (a >> 18));
		c ^= b; c -= ((b << 24) | (b >> 8));
		return c;
	}
	
	public static int hashHsieh(int init, Object... vals) {
		if (vals == null || vals.length == 0) return init;
		int hash = init;
		/* Main loop */
		for (Object o : vals) {
			int thingHash = o.hashCode();
			hash += (thingHash >>> 16);
			int tmp = ((thingHash & 0xffff) << 11) ^ hash;
			hash = (hash << 16) ^ tmp;
			hash += (hash >> 11);
		}

		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3;
		hash += hash >> 5;
		hash ^= hash << 4;
		hash += hash >> 17;
		hash ^= hash << 25;
		hash += hash >> 6;
		return hash;
	}
	
	public static int hashHsieh(int init, Object val) {
		int hash = init;
		int thingHash = val.hashCode();
		hash += (thingHash >>> 16);
		int tmp = ((thingHash & 0xffff) << 11) ^ hash;
		hash = (hash << 16) ^ tmp;
		hash += (hash >> 11);
		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3;
		hash += hash >> 5;
		hash ^= hash << 4;
		hash += hash >> 17;
		hash ^= hash << 25;
		hash += hash >> 6;
		return hash;
	}
	
}
