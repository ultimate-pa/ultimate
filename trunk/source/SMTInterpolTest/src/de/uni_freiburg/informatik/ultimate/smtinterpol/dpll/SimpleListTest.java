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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class SimpleListTest {
	class Elem extends SimpleListable<Elem> {
		int mVal;

		public Elem(final int i) {
			mVal = i;
		}

		@Override
		public String toString() {
			return String.valueOf(mVal);
		}
	}

	@Test
	public void testAppendPrepend() {
		final SimpleList<Elem> l = new SimpleList<>();
		l.append(new Elem(3));// NOCHECKSTYLE
		l.append(new Elem(4));// NOCHECKSTYLE
		l.prepend(new Elem(2));
		l.append(new Elem(5));// NOCHECKSTYLE
		l.prepend(new Elem(1));
		Assert.assertTrue(l.wellformed());
		Assert.assertEquals("[1,2,3,4,5]", l.toString());
		l.clear();
		l.prepend(new Elem(3));// NOCHECKSTYLE
		l.append(new Elem(4));// NOCHECKSTYLE
		l.prepend(new Elem(2));
		l.append(new Elem(5));// NOCHECKSTYLE
		l.prepend(new Elem(1));
		Assert.assertTrue(l.wellformed());
		Assert.assertEquals("[1,2,3,4,5]", l.toString());
	}

	@Test
	public void testJoinBorder() {
		final SimpleList<Elem> la = new SimpleList<>();
		la.prependIntoJoined(new Elem(3), true);// NOCHECKSTYLE
		la.prependIntoJoined(new Elem(2), true);
		la.prependIntoJoined(new Elem(1), true);
		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2,3]", la.toString());
	}

	@Test
	public void testLinearJoins() {
		final SimpleList<Elem> la = new SimpleList<>();
		final SimpleList<Elem> lb = new SimpleList<>();
		final SimpleList<Elem> lc = new SimpleList<>();
		final SimpleList<Elem> ld = new SimpleList<>();

		la.append(new Elem(1));
		la.append(new Elem(2));
		lc.append(new Elem(4));// NOCHECKSTYLE

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2]", la.toString());
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[]", lb.toString());
		Assert.assertTrue(lc.wellformed());
		Assert.assertEquals("[4]", lc.toString());
		Assert.assertTrue(ld.wellformed());
		Assert.assertEquals("[]", ld.toString());

		lc.joinList(ld);
		Assert.assertTrue(lc.wellformed());
		Assert.assertEquals("[4]", lc.toString());
		lb.joinList(lc);
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[4]", lb.toString());
		la.joinList(lb);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2,4]", la.toString());
		Assert.assertTrue(lb.wellformedPart());
		Assert.assertTrue(lc.wellformedPart());
		Assert.assertTrue(ld.wellformedPart());

		final Elem e3 = new Elem(3);// NOCHECKSTYLE
		lc.prependIntoJoined(e3, false);
		lb.prependIntoJoined(e3, false);
		la.prependIntoJoined(e3, true);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2,3,4]", la.toString());
		Assert.assertTrue(lb.wellformedPart());
		Assert.assertTrue(lc.wellformedPart());
		Assert.assertTrue(ld.wellformedPart());

		final Elem e5 = new Elem(5);// NOCHECKSTYLE
		ld.prependIntoJoined(e5, false);
		lc.prependIntoJoined(e5, false);
		lb.prependIntoJoined(e5, false);
		la.prependIntoJoined(e5, true);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2,5,3,4]", la.toString());
		Assert.assertTrue(lb.wellformedPart());
		Assert.assertTrue(lc.wellformedPart());
		Assert.assertTrue(ld.wellformedPart());

		la.unjoinList(lb);
		lb.unjoinList(lc);
		lc.unjoinList(ld);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2]", la.toString());
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[]", lb.toString());
		Assert.assertTrue(lc.wellformed());
		Assert.assertEquals("[3,4]", lc.toString());
		Assert.assertTrue(ld.wellformed());
		Assert.assertEquals("[5]", ld.toString());
	}

	@Test
	public void testTreeJoins() {
		final SimpleList<Elem> la = new SimpleList<>();
		final SimpleList<Elem> lb = new SimpleList<>();
		final SimpleList<Elem> lc = new SimpleList<>();
		final SimpleList<Elem> ld = new SimpleList<>();
		final SimpleList<Elem> le = new SimpleList<>();

		lb.append(new Elem(1));
		lb.append(new Elem(2));
		le.append(new Elem(4));// NOCHECKSTYLE

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[]", la.toString());
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[1,2]", lb.toString());
		Assert.assertTrue(lc.wellformed());
		Assert.assertEquals("[]", lc.toString());
		Assert.assertTrue(ld.wellformed());
		Assert.assertEquals("[]", ld.toString());
		Assert.assertTrue(le.wellformed());
		Assert.assertEquals("[4]", le.toString());

		lb.joinList(lc);
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[1,2]", lb.toString());
		ld.joinList(le);
		Assert.assertTrue(ld.wellformed());
		Assert.assertEquals("[4]", ld.toString());
		la.joinList(lb);
		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2]", la.toString());
		la.joinList(ld);
		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[1,2,4]", la.toString());
		Assert.assertTrue(lb.wellformedPart());
		Assert.assertTrue(lc.wellformedPart());
		Assert.assertTrue(ld.wellformedPart());
		Assert.assertTrue(le.wellformedPart());

		final Elem e3 = new Elem(3);// NOCHECKSTYLE
		lc.prependIntoJoined(e3, false);
		lb.prependIntoJoined(e3, false);
		la.prependIntoJoined(e3, true);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[3,1,2,4]", la.toString());
		Assert.assertTrue(lb.wellformedPart());
		Assert.assertTrue(lc.wellformedPart());

		final Elem e5 = new Elem(5);// NOCHECKSTYLE
		le.prependIntoJoined(e5, false);
		ld.prependIntoJoined(e5, false);
		la.prependIntoJoined(e5, true);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[3,1,2,5,4]", la.toString());
		Assert.assertTrue(ld.wellformedPart());
		Assert.assertTrue(le.wellformedPart());

		la.unjoinList(lb);
		lb.unjoinList(lc);
		la.unjoinList(ld);
		ld.unjoinList(le);

		Assert.assertTrue(la.wellformed());
		Assert.assertEquals("[]", la.toString());
		Assert.assertTrue(lb.wellformed());
		Assert.assertEquals("[1,2]", lb.toString());
		Assert.assertTrue(lc.wellformed());
		Assert.assertEquals("[3]", lc.toString());
		Assert.assertTrue(ld.wellformed());
		Assert.assertEquals("[]", ld.toString());
		Assert.assertTrue(le.wellformed());
		Assert.assertEquals("[5,4]", le.toString());
	}
}
