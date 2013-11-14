/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import junit.framework.TestCase;


public class SimpleListTest extends TestCase {
	class Elem extends SimpleListable<Elem> {
		int val;
		
		public Elem(int i) {
			val = i;
		}
		
		public String toString() {
			return String.valueOf(val);
		}
	}
	
	public void testAppendPrepend() {
		SimpleList<Elem> l = new SimpleList<Elem>();
		l.append(new Elem(3));
		l.append(new Elem(4));
		l.prepend(new Elem(2));
		l.append(new Elem(5));
		l.prepend(new Elem(1));
		assertTrue(l.wellformed());
		assertEquals("[1,2,3,4,5]", l.toString());
		l.clear();
		l.prepend(new Elem(3));
		l.append(new Elem(4));
		l.prepend(new Elem(2));
		l.append(new Elem(5));
		l.prepend(new Elem(1));
		assertTrue(l.wellformed());
		assertEquals("[1,2,3,4,5]", l.toString());
	}
	
	public void testJoinBorder() {
		SimpleList<Elem> la = new SimpleList<Elem>();
		la.prependIntoJoined(new Elem(3), true);
		la.prependIntoJoined(new Elem(2), true);
		la.prependIntoJoined(new Elem(1), true);
		assertTrue(la.wellformed());
		assertEquals("[1,2,3]", la.toString());
	}
	
	public void testLinearJoins() {
		SimpleList<Elem> la = new SimpleList<Elem>();
		SimpleList<Elem> lb = new SimpleList<Elem>();
		SimpleList<Elem> lc = new SimpleList<Elem>();
		SimpleList<Elem> ld = new SimpleList<Elem>();
		
		la.append(new Elem(1));
		la.append(new Elem(2));
		lc.append(new Elem(4));
		
		assertTrue(la.wellformed());
		assertEquals("[1,2]", la.toString());
		assertTrue(lb.wellformed());
		assertEquals("[]", lb.toString());
		assertTrue(lc.wellformed());
		assertEquals("[4]", lc.toString());
		assertTrue(ld.wellformed());
		assertEquals("[]", ld.toString());
		
		lc.joinList(ld);
		assertTrue(lc.wellformed());
		assertEquals("[4]", lc.toString());
		lb.joinList(lc);
		assertTrue(lb.wellformed());
		assertEquals("[4]", lb.toString());
		la.joinList(lb);

		assertTrue(la.wellformed());
		assertEquals("[1,2,4]", la.toString());
		assertTrue(lb.wellformedPart());
		assertTrue(lc.wellformedPart());
		assertTrue(ld.wellformedPart());
		
		Elem e3 = new Elem(3);
		lc.prependIntoJoined(e3, false);
		lb.prependIntoJoined(e3, false);
		la.prependIntoJoined(e3, true);
		
		assertTrue(la.wellformed());
		assertEquals("[1,2,3,4]", la.toString());
		assertTrue(lb.wellformedPart());
		assertTrue(lc.wellformedPart());
		assertTrue(ld.wellformedPart());

		Elem e5 = new Elem(5);
		ld.prependIntoJoined(e5, false);
		lc.prependIntoJoined(e5, false);
		lb.prependIntoJoined(e5, false);
		la.prependIntoJoined(e5, true);

		assertTrue(la.wellformed());
		assertEquals("[1,2,5,3,4]", la.toString());
		assertTrue(lb.wellformedPart());
		assertTrue(lc.wellformedPart());
		assertTrue(ld.wellformedPart());
		
		la.unjoinList(lb);
		lb.unjoinList(lc);
		lc.unjoinList(ld);


		assertTrue(la.wellformed());
		assertEquals("[1,2]", la.toString());
		assertTrue(lb.wellformed());
		assertEquals("[]", lb.toString());
		assertTrue(lc.wellformed());
		assertEquals("[3,4]", lc.toString());
		assertTrue(ld.wellformed());
		assertEquals("[5]", ld.toString());
	}

	public void testTreeJoins() {
		SimpleList<Elem> la = new SimpleList<Elem>();
		SimpleList<Elem> lb = new SimpleList<Elem>();
		SimpleList<Elem> lc = new SimpleList<Elem>();
		SimpleList<Elem> ld = new SimpleList<Elem>();
		SimpleList<Elem> le = new SimpleList<Elem>();
		
		lb.append(new Elem(1));
		lb.append(new Elem(2));
		le.append(new Elem(4));
		
		assertTrue(la.wellformed());
		assertEquals("[]", la.toString());
		assertTrue(lb.wellformed());
		assertEquals("[1,2]", lb.toString());
		assertTrue(lc.wellformed());
		assertEquals("[]", lc.toString());
		assertTrue(ld.wellformed());
		assertEquals("[]", ld.toString());
		assertTrue(le.wellformed());
		assertEquals("[4]", le.toString());
		
		lb.joinList(lc);
		assertTrue(lb.wellformed());
		assertEquals("[1,2]", lb.toString());
		ld.joinList(le);
		assertTrue(ld.wellformed());
		assertEquals("[4]", ld.toString());
		la.joinList(lb);
		assertTrue(la.wellformed());
		assertEquals("[1,2]", la.toString());
		la.joinList(ld);
		assertTrue(la.wellformed());
		assertEquals("[1,2,4]", la.toString());
		assertTrue(lb.wellformedPart());
		assertTrue(lc.wellformedPart());
		assertTrue(ld.wellformedPart());
		assertTrue(le.wellformedPart());
		
		Elem e3 = new Elem(3);
		lc.prependIntoJoined(e3, false);
		lb.prependIntoJoined(e3, false);
		la.prependIntoJoined(e3, true);
		
		assertTrue(la.wellformed());
		assertEquals("[3,1,2,4]", la.toString());
		assertTrue(lb.wellformedPart());
		assertTrue(lc.wellformedPart());

		Elem e5 = new Elem(5);
		le.prependIntoJoined(e5, false);
		ld.prependIntoJoined(e5, false);
		la.prependIntoJoined(e5, true);

		assertTrue(la.wellformed());
		assertEquals("[3,1,2,5,4]", la.toString());
		assertTrue(ld.wellformedPart());
		assertTrue(le.wellformedPart());
		
		la.unjoinList(lb);
		lb.unjoinList(lc);
		la.unjoinList(ld);
		ld.unjoinList(le);


		assertTrue(la.wellformed());
		assertEquals("[]", la.toString());
		assertTrue(lb.wellformed());
		assertEquals("[1,2]", lb.toString());
		assertTrue(lc.wellformed());
		assertEquals("[3]", lc.toString());
		assertTrue(ld.wellformed());
		assertEquals("[]", ld.toString());
		assertTrue(le.wellformed());
		assertEquals("[5,4]", le.toString());
	}
}
