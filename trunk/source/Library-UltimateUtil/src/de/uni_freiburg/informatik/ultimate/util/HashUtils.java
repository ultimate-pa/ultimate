/*
 * Copyright (C) 2012-2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.util;

/**
 * This implements Jenkins und Hsieh hash functions. It is based on the code at
 * <a href="http://www.burtleburtle.net/bob/c/lookup3.c">http://www.burtleburtle.net/bob/c/lookup3.c</a>.
 *
 *
 * @author Jürgen Christ, Jochen Hoenicke
 *
 */
public final class HashUtils {
	private final static int BASE = 0xdeadbeef;

	private HashUtils() {
		// Hide constructor
	}

	public static int hashJenkins(final int init, final byte[] vals) {
		if (vals == null || vals.length == 0) {
			return init;
		}
		int a,b,c;
		a = b = c = BASE + (vals.length << 2) + init;
		int pos = 0;
		while (vals.length - pos > 12) {
			a += (vals[pos] & 0xff) + ((vals[pos + 1] & 0xff) << 8) + ((vals[pos + 2] & 0xff) << 16)
					+ ((vals[pos + 3] & 0xff) << 24);
			b += (vals[pos + 4] & 0xff) + ((vals[pos + 5] & 0xff) << 8) + ((vals[pos + 6] & 0xff) << 16)
					+ ((vals[pos + 7] & 0xff) << 24);
			c += (vals[pos + 8] & 0xff) + ((vals[pos + 9] & 0xff) << 8) + ((vals[pos + 10] & 0xff) << 16)
					+ ((vals[pos + 11] & 0xff) << 24);
			// This is the mix function of Jenkins hash.
			// Note that we need >>> for unsigned shift.
			// rot(c,4) is ((c << 4) | (c >>> 28)).
			a -= c;
			a ^= ((c << 4) | (c >>> 28));
			c += b;
			b -= a;
			b ^= ((a << 6) | (a >>> 26));
			a += c;
			c -= b;
			c ^= ((b << 8) | (b >>> 24));
			b += a;
			a -= c;
			a ^= ((c << 16) | (c >>> 16));
			c += b;
			b -= a;
			b ^= ((a << 19) | (a >>> 13));
			a += c;
			c -= b;
			c ^= ((b << 4) | (b >>> 28));
			b += a;
			pos += 3;
		}
		switch (vals.length - pos) {
		case 12:
			c += (vals[pos + 11] & 0xff) << 24;
			//$FALL-THROUGH$
		case 11:
			c += (vals[pos + 10] & 0xff) << 16;
			//$FALL-THROUGH$
		case 10:
			c += (vals[pos + 9] & 0xff) << 8;
			//$FALL-THROUGH$
		case 9:
			c += (vals[pos + 8] & 0xff);
			//$FALL-THROUGH$
		case 8:
			b += (vals[pos + 7] & 0xff) << 24;
			//$FALL-THROUGH$
		case 7:
			b += (vals[pos + 6] & 0xff) << 16;
			//$FALL-THROUGH$
		case 6:
			b += (vals[pos + 5] & 0xff) << 8;
			//$FALL-THROUGH$
		case 5:
			b += (vals[pos + 4] & 0xff);
			//$FALL-THROUGH$
		case 4:
			a += (vals[pos + 3] & 0xff) << 24;
			//$FALL-THROUGH$
		case 3:
			a += (vals[pos + 2] & 0xff) << 16;
			//$FALL-THROUGH$
		case 2:
			a += (vals[pos + 1] & 0xff) << 8;
			//$FALL-THROUGH$
		case 1:
			a += (vals[pos] & 0xff);
			// This is the final mix function of Jenkins hash.
			c ^= b;
			c -= ((b << 14) | (b >>> 18));
			a ^= c;
			a -= ((c << 11) | (c >>> 21));
			b ^= a;
			b -= ((a << 25) | (a >>> 7));
			c ^= b;
			c -= ((b << 16) | (b >>> 16));
			a ^= c;
			a -= ((c << 4) | (c >>> 28));
			b ^= a;
			b -= ((a << 14) | (a >>> 18));
			c ^= b;
			c -= ((b << 24) | (b >>> 8));
			//$FALL-THROUGH$
		case 0:
			//$FALL-THROUGH$
		default:
			break;
		}
		return c;
	}

	public static int hashJenkins(final int init, final Object... vals) {
		if (vals == null || vals.length == 0) {
			return init;
		}
		int a,b,c;
		a = b = c = BASE + (vals.length << 2) + init;
		int pos = 0;
		while (vals.length - pos > 3) {
			a += vals[pos].hashCode();
			b += vals[pos + 1].hashCode();
			c += vals[pos + 2].hashCode();
			// This is the mix function of Jenkins hash.
			// Note that we need >>> for unsigned shift.
			// rot(c,4) is ((c << 4) | (c >>> 28)).
			a -= c;
			a ^= ((c << 4) | (c >>> 28));
			c += b;
			b -= a;
			b ^= ((a << 6) | (a >>> 26));
			a += c;
			c -= b;
			c ^= ((b << 8) | (b >>> 24));
			b += a;
			a -= c;
			a ^= ((c << 16) | (c >>> 16));
			c += b;
			b -= a;
			b ^= ((a << 19) | (a >>> 13));
			a += c;
			c -= b;
			c ^= ((b << 4) | (b >>> 28));
			b += a;
			pos += 3;
		}
		switch (vals.length - pos) {
		case 3:
			c += vals[pos++].hashCode();
			// fallthrough
		case 2:
			b += vals[pos++].hashCode();
			// fallthrough
		case 1:
			a += vals[pos].hashCode();
			// This is the final mix function of Jenkins hash.
			c ^= b;
			c -= ((b << 14) | (b >>> 18));
			a ^= c;
			a -= ((c << 11) | (c >>> 21));
			b ^= a;
			b -= ((a << 25) | (a >>> 7));
			c ^= b;
			c -= ((b << 16) | (b >>> 16));
			a ^= c;
			a -= ((c << 4) | (c >>> 28));
			b ^= a;
			b -= ((a << 14) | (a >>> 18));
			c ^= b;
			c -= ((b << 24) | (b >>> 8));
			// fallthrough
		case 0:
			// fallthrough
		default:
			break;
		}
		return c;
	}

	public static int hashJenkins(final int init, final Object val) {
		int a,b,c;
		a = b = BASE + 4 + init;
		// slightly optimized version of hashJenkins(init, new Object[] {val})
		a += val.hashCode();
		c = -((b << 14) | (b >>> 18));
		a ^= c;
		a -= ((c << 11) | (c >>> 21));
		b ^= a;
		b -= ((a << 25) | (a >>> 7));
		c ^= b;
		c -= ((b << 16) | (b >>> 16));
		a ^= c;
		a -= ((c << 4) | (c >>> 28));
		b ^= a;
		b -= ((a << 14) | (a >>> 18));
		c ^= b;
		c -= ((b << 24) | (b >>> 8));
		return c;
	}

	public static int hashHsieh(final int init, final Object... vals) {
		if (vals == null || vals.length == 0) {
			return init;
		}
		int hash = init;
		/* Main loop */
		for (final Object o : vals) {
			final int thingHash = o.hashCode();
			hash += (thingHash >>> 16);
			final int tmp = ((thingHash & 0xffff) << 11) ^ hash;
			hash = (hash << 16) ^ tmp;
			hash += (hash >>> 11);
		}

		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3;
		hash += hash >>> 5;
		hash ^= hash << 4;
		hash += hash >>> 17;
		hash ^= hash << 25;
		hash += hash >>> 6;
		return hash;
	}

	public static int hashHsieh(final int init, final Object val) {
		int hash = init;
		final int thingHash = val.hashCode();
		hash += (thingHash >>> 16);
		final int tmp = ((thingHash & 0xffff) << 11) ^ hash;
		hash = (hash << 16) ^ tmp;
		hash += (hash >>> 11);
		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3;
		hash += hash >>> 5;
		hash ^= hash << 4;
		hash += hash >>> 17;
		hash ^= hash << 25;
		hash += hash >>> 6;
		return hash;
	}

}
