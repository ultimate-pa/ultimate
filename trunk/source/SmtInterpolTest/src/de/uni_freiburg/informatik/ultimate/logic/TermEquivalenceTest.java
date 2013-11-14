package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermEquivalence;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import junit.framework.TestCase;

public class TermEquivalenceTest extends TestCase {
	public void testEq() {
		Theory theory = new Theory(Logics.AUFLIRA);
		// (let ((x y)) (forall ((y Int)) (>= y x)))
		// (let ((z y)) (forall ((w Int)) (>= w z)))
		Sort intSort = theory.getNumericSort();
		TermVariable x = theory.createTermVariable("x", intSort);
		TermVariable y = theory.createTermVariable("y", intSort);
		TermVariable z = theory.createTermVariable("z", intSort);
		TermVariable w = theory.createTermVariable("w", intSort);
		Term lhs = theory.let(x, y, 
				theory.forall(new TermVariable[]{y}, theory.term(">=", y, x)));
		Term rhs = theory.let(z, y, 
				theory.forall(new TermVariable[]{w}, theory.term(">=", w, z)));
		assert (new TermEquivalence().equal(lhs, rhs));
	}
}
