/*
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;


import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;


/**
 * Tests for {@link SimplifyBdd}
 * @author Michael Steinle
 *
 */
public class SimplifyBddTest {
	
	IUltimateServiceProvider services;
	Script script;
	SimplifyBdd simplifyBdd;
	Sort bool;
	Sort ints;
	
	@Before
	public void setUP(){
		services = new UltimateServiceProviderMock();
		script = new SMTInterpol();
		final IFreshTermVariableConstructor freshTermVariableConstructor = null;
		simplifyBdd = new SimplifyBdd(services, script, freshTermVariableConstructor);

		script.setLogic(Logics.QF_IDL);
		bool = ((SMTInterpol)script).getTheory().getBooleanSort();
		ints = ((SMTInterpol)script).getTheory().getNumericSort();
	}
	
	
	@Test
	public void testAtomCollection() {
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term x3 = script.variable("x3", bool);
		Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1,x2,x3)), x1));
		
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(t);
		Assert.assertTrue(atoms.contains(x1));
		Assert.assertTrue(atoms.contains(x2));
		Assert.assertTrue(atoms.contains(x3));
		Assert.assertEquals(3, atoms.size());
	}
	
	@Test
	public void testTransform() {
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term x3 = script.variable("x3", bool);
		Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1,x2,x3)), x1));
		Term out = simplifyBdd.transform(t); 
		Assert.assertEquals(x1, out);
	}

	
	@Test
	public void testCNF() {
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term x3 = script.variable("x3", bool);
		Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1,x2,x3)), x1));
		Term out = simplifyBdd.transformToCNF(t);
		Assert.assertEquals(x1, out);
	}
	
	@Test
	public void testDNF() {
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term x3 = script.variable("x3", bool);
		Term t = SmtUtils.or(script, Arrays.asList(SmtUtils.and(script, Arrays.asList(x1,x2,x3)), x1));
		Term out = simplifyBdd.transformToDNF(t);
		Assert.assertEquals(x1, out);
	}
	
	@Test
	public void testAssozImp(){
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term x3 = script.variable("x3", bool);
		Term t1 = script.term("=>", x1, x2, x3);
		Term t2 = script.term("=>", x1, script.term("=>", x2, x3));
		Term t3 = script.term("=>", script.term("=>", x1, x2), x3) ;

		Term out1 = simplifyBdd.transform(t1);
		Term out2 = simplifyBdd.transform(t2);
		Term out3 = simplifyBdd.transform(t3);
		Assert.assertEquals(out2, out1);
		Assert.assertNotEquals(out3, out1);
	}
	
	@Test
	public void testPairImp(){
		//Term t1 = script.term("<", script.variable("x", ints), script.numeral("2"));
		//Term t2 = script.term("<", script.variable("x", ints), script.numeral("3"));
		Term t1 = script.term("<", script.numeral("1"), script.numeral("2"));
		Term t2 = script.term("<", script.numeral("1"), script.numeral("3"));
		simplifyBdd.impliesPairwise(Arrays.asList(t1,t2));	
	}
	
}
