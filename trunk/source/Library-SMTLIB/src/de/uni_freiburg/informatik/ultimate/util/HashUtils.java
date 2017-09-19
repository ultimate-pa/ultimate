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

public final class HashUtils {
	
	// deadbeaf leads to hash conflicts on f...
	private final static int BASE = 0xcafebabe;
	
	private HashUtils() {
		// Hide constructor
	}
	
	public static int hashJenkins(int init, Object... vals) {
		if (vals == null || vals.length == 0) {
			return init;
		}
		int a,b,c;
		a = b = c = BASE + (vals.length << 2) + init;
		int pos = 0;
		while (vals.length - pos > 3) { //NOCHECKSTYLE
			a += vals[pos].hashCode();
			b += vals[pos + 1].hashCode();
			c += vals[pos + 2].hashCode();
			a -= c; a ^= ((c << 4) | (c >> 28)); c += b; //NOCHECKSTYLE
			b -= a; b ^= ((a << 6) | (c >> 26)); a += c; //NOCHECKSTYLE
			c -= b; c ^= ((b << 8) | (b >> 24)); b += a; //NOCHECKSTYLE
			a -= c; a ^= ((c << 16) | (c >> 16)); c += b; //NOCHECKSTYLE
			b -= a; b ^= ((a << 19) | (c >> 13)); a += c; //NOCHECKSTYLE
			c -= b; c ^= ((b << 4) | (b >> 28)); b += a; //NOCHECKSTYLE
			pos += 3; //NOCHECKSTYLE
		}
		switch (vals.length - pos) {
		case 3: c += vals[pos++].hashCode(); //NOCHECKSTYLE
		case 2: b += vals[pos++].hashCode(); //NOCHECKSTYLE
		case 1: a += vals[pos].hashCode(); //NOCHECKSTYLE
			c ^= b; c -= ((b << 14) | (b >> 18)); //NOCHECKSTYLE
			a ^= c; a -= ((c << 11) | (c >> 21)); //NOCHECKSTYLE
			b ^= a; b -= ((a << 25) | (a >> 7)); //NOCHECKSTYLE
			c ^= b; c -= ((b << 16) | (b >> 16)); //NOCHECKSTYLE
			a ^= c; a -= ((c << 4) | (c >> 28)); //NOCHECKSTYLE
			b ^= a; b -= ((a << 14) | (a >> 18)); //NOCHECKSTYLE
			c ^= b; c -= ((b << 24) | (b >> 8)); //NOCHECKSTYLE
			// fallthrough
		case 0:
			// fallthrough
		default:
			break;
		}
		return c;
	}
	
	public static int hashJenkins(int init, Object val) {
		int a,b,c;
		a = b = BASE + 4 + init; //NOCHECKSTYLE
		a += val.hashCode();
		c = -((b << 14) | (b >> 18)); //NOCHECKSTYLE
		a ^= c; a -= ((c << 11) | (c >> 21)); //NOCHECKSTYLE
		b ^= a; b -= ((a << 25) | (a >> 7)); //NOCHECKSTYLE
		c ^= b; c -= ((b << 16) | (b >> 16)); //NOCHECKSTYLE
		a ^= c; a -= ((c << 4) | (c >> 28)); //NOCHECKSTYLE
		b ^= a; b -= ((a << 14) | (a >> 18)); //NOCHECKSTYLE
		c ^= b; c -= ((b << 24) | (b >> 8)); //NOCHECKSTYLE
		return c;
	}
	
	public static int hashHsieh(int init, Object... vals) {
		if (vals == null || vals.length == 0) {
			return init;
		}
		int hash = init;
		/* Main loop */
		for (final Object o : vals) {
			final int thingHash = o.hashCode();
			hash += (thingHash >>> 16); //NOCHECKSTYLE
			final int tmp = ((thingHash & 0xffff) << 11) ^ hash; //NOCHECKSTYLE
			hash = (hash << 16) ^ tmp; //NOCHECKSTYLE
			hash += (hash >> 11); //NOCHECKSTYLE
		}

		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3; //NOCHECKSTYLE
		hash += hash >> 5; //NOCHECKSTYLE
		hash ^= hash << 4; //NOCHECKSTYLE
		hash += hash >> 17; //NOCHECKSTYLE
		hash ^= hash << 25; //NOCHECKSTYLE
		hash += hash >> 6; //NOCHECKSTYLE
		return hash;
	}
	
	public static int hashHsieh(int init, Object val) {
		int hash = init;
		final int thingHash = val.hashCode();
		hash += (thingHash >>> 16); //NOCHECKSTYLE
		final int tmp = ((thingHash & 0xffff) << 11) ^ hash; //NOCHECKSTYLE
		hash = (hash << 16) ^ tmp; //NOCHECKSTYLE
		hash += (hash >> 11); //NOCHECKSTYLE
		/* Force "avalanching" of final 127 bits */
		hash ^= hash << 3; //NOCHECKSTYLE
		hash += hash >> 5; //NOCHECKSTYLE
		hash ^= hash << 4; //NOCHECKSTYLE
		hash += hash >> 17; //NOCHECKSTYLE
		hash ^= hash << 25; //NOCHECKSTYLE
		hash += hash >> 6; //NOCHECKSTYLE
		return hash;
	}
	
}
