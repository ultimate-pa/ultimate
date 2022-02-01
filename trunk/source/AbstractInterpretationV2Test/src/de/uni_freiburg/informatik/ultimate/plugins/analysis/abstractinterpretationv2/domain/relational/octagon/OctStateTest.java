package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.FakeBoogieVar;

public class OctStateTest {

	@Test
	public void testIntersect() {

		final FakeBoogieVar varA = new FakeBoogieVar(BoogieType.TYPE_INT, "a");
		final FakeBoogieVar varB = new FakeBoogieVar(BoogieType.TYPE_INT, "b");
		final FakeBoogieVar varC = new FakeBoogieVar(BoogieType.TYPE_INT, "c");

		OctDomainState s1 = OctDomainState.createFreshState(a -> a.logStringHalfMatrix());
		OctDomainState s2 = OctDomainState.createFreshState(a -> a.logStringHalfMatrix());

		s1 = s1.addVariable(varC);
		s1 = s1.addVariable(varA);
		s1 = s1.addVariable(varB);

		s2 = s2.addVariable(varA);
		s2 = s2.addVariable(varB);
		s2 = s2.addVariable(varC);

		s1.assumeNumericVarConstant(varA, OctValue.parse("19"));
		s1.assumeNumericVarConstant(varB, OctValue.parse("1"));

		s2.assignNumericVarConstant(varC, OctValue.parse("0"));

		final OctDomainState s3 = s1.intersect(s2);
		final OctDomainState s4 = s2.intersect(s1);

		Assert.assertEquals("s3 is bottom, but should not be", false, s3.isBottom());
		Assert.assertEquals("s3 and s4 should be equal", true, s3.isEqualTo(s4));
	}

}
