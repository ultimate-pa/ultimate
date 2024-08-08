/*
 * Copyright (C) 2020-2021 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2020-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 *
 * @author Max Barth
 */
@RunWith(JUnit4.class)
public class BitvectorTest {

	private SMTInterpol mSolver;

	private Term a;
	private Term b;
	private Term c;
	private Term x;
	private Term y;
	private Term z;
	private Term u;
	private Term v;
	private Term w;
	private Term p;
	private Term q;
	private Term p2;
	private Term q2;
	private Term p3;
	private Term q3;
	private Term p4;
	private Term q4;
	private Term p7;
	private Term p8;
	private Term q8;

	@Before
	public void setUp() throws Exception {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setOption(":produce-models", Boolean.TRUE);
		mSolver.setOption(":model-check-mode", Boolean.TRUE);
		mSolver.setOption(":proof-check-mode", Boolean.TRUE);
		mSolver.setOption(":verbosity", 8);
		mSolver.setLogic(Logics.ALL); // TODO declare numeric Sort if logic is bv
		final Sort bv1 = mSolver.getTheory().getSort("BitVec", new String[] { "1" });
		final Sort bv2 = mSolver.getTheory().getSort("BitVec", new String[] { "2" });
		final Sort bv3 = mSolver.getTheory().getSort("BitVec", new String[] { "3" });
		final Sort bv4 = mSolver.getTheory().getSort("BitVec", new String[] { "4" });
		final Sort bv7 = mSolver.getTheory().getSort("BitVec", new String[] { "7" });
		final Sort bv8 = mSolver.getTheory().getSort("BitVec", new String[] { "8" });
		final Sort bv12 = mSolver.getTheory().getSort("BitVec", new String[] { "12" });
		final Sort bv16 = mSolver.getTheory().getSort("BitVec", new String[] { "16" });
		final Sort bv32 = mSolver.getTheory().getSort("BitVec", new String[] { "32" });

		mSolver.declareFun("x", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("y", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("z", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("a", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("b", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("c", Script.EMPTY_SORT_ARRAY, bv16);

		mSolver.declareFun("u", Script.EMPTY_SORT_ARRAY, bv32);
		mSolver.declareFun("v", Script.EMPTY_SORT_ARRAY, bv32);
		mSolver.declareFun("w", Script.EMPTY_SORT_ARRAY, bv32);

		mSolver.declareFun("p", Script.EMPTY_SORT_ARRAY, bv1);
		mSolver.declareFun("q", Script.EMPTY_SORT_ARRAY, bv1);
		mSolver.declareFun("p2", Script.EMPTY_SORT_ARRAY, bv2);
		mSolver.declareFun("q2", Script.EMPTY_SORT_ARRAY, bv2);
		mSolver.declareFun("p3", Script.EMPTY_SORT_ARRAY, bv3);
		mSolver.declareFun("q3", Script.EMPTY_SORT_ARRAY, bv3);
		mSolver.declareFun("p4", Script.EMPTY_SORT_ARRAY, bv4);
		mSolver.declareFun("q4", Script.EMPTY_SORT_ARRAY, bv4);
		mSolver.declareFun("q8", Script.EMPTY_SORT_ARRAY, bv8);
		mSolver.declareFun("p8", Script.EMPTY_SORT_ARRAY, bv8);
		mSolver.declareFun("p7", Script.EMPTY_SORT_ARRAY, bv7);

		x = mSolver.term("x");
		y = mSolver.term("y");
		z = mSolver.term("z");
		a = mSolver.term("a");
		b = mSolver.term("b");
		c = mSolver.term("c");

		u = mSolver.term("u");
		v = mSolver.term("v");
		w = mSolver.term("w");

		p = mSolver.term("p");
		q = mSolver.term("q");
		p2 = mSolver.term("p2");
		q2 = mSolver.term("q2");
		p3 = mSolver.term("p3");
		q3 = mSolver.term("q3");
		p4 = mSolver.term("p4");
		q4 = mSolver.term("q4");
		p7 = mSolver.term("p7");
		p8 = mSolver.term("p8");
		q8 = mSolver.term("q8");
	}

	@After
	public void tearDown() throws Exception {
		mSolver.exit();
		mSolver = null;
	}

	@Test
	public void constRelations1() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm1 = mSolver.binary("#b1001");
		final Term input = mSolver.term("and", mSolver.term("=", consTerm, consTerm),
				mSolver.term("bvult", consTerm, consTerm1), mSolver.term("bvule", consTerm, consTerm),
				mSolver.term("bvugt", consTerm1, consTerm), mSolver.term("bvuge", consTerm, consTerm));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isunSat);
		mSolver.reset();
	}

	@Test
	public void constRelations2() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "4";

		final Term consTerm = mSolver.term("bv3", constindices, null);
		final Term consTerm1 = mSolver.term("bv4", constindices, null);
		final Term input = mSolver.term("and", mSolver.term("bvslt", consTerm1, consTerm),
				mSolver.term("bvsle", consTerm, consTerm), mSolver.term("bvsgt", consTerm, consTerm1));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isunSat);
		mSolver.reset();
	}

	@Test
	public void constRelations3() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm1 = mSolver.binary("#b1001");
		final Term input =
				mSolver.term("and", mSolver.term("bvslt", consTerm1, consTerm), mSolver.term("bvsle", p4, p4),
						mSolver.term("bvsgt", consTerm, consTerm1), mSolver.term("bvsge", consTerm, consTerm));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isunSat);
		mSolver.reset();
	}

	@Test
	public void constFunctions() {
		// {bvand, bvor, bvadd, bvmul, bvudiv, bvurem}
		mSolver.resetAssertions();

		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm2 = mSolver.binary("#b0010"); // "(_ bv2 4)"
		final Term consTerm3 = mSolver.hexadecimal("#x3");
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("bvadd", consTerm, consTerm), consTerm2),
				mSolver.term("=", mSolver.term("bvmul", consTerm, consTerm), consTerm),
				mSolver.term("=", mSolver.term("bvudiv", consTerm2, consTerm), consTerm2),
				mSolver.term("=", mSolver.term("concat", consTerm, mSolver.term("bvadd", consTerm2, consTerm)),
						mSolver.term("concat", consTerm, consTerm3)),
				mSolver.term("=", mSolver.term("bvand", consTerm2, consTerm3), consTerm2),
				mSolver.term("=", mSolver.term("bvor", consTerm, consTerm2), consTerm3),
				mSolver.term("=", mSolver.term("bvurem", consTerm3, consTerm2), consTerm),
				mSolver.term("=", mSolver.term("bvnot", consTerm3), consTerm),
				mSolver.term("=", mSolver.term("bvneg", consTerm), consTerm));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);

	}

	@Test
	public void constSelect() {
		mSolver.resetAssertions();
		// final Term consTerm = mSolver.term("(_ bv 4 4)");
		final String[] asd = new String[2];
		asd[0] = "7";
		asd[1] = "5";
		final Term consTerm1 = mSolver.binary("#b00100000");
		final Term consTerm2 = mSolver.binary("#b00100010");
		final Term term1 = mSolver.term("extract", asd, null, consTerm1);
		final Term term2 = mSolver.term("extract", asd, null, consTerm2);
		final Term input = mSolver.term("=", term1, term2);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void constConcat() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b01110100"),
				mSolver.term("concat", mSolver.binary("#b0111"), mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void constShift() {
		// {bvshl, bvlshr}
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b1001");
		final Term consTerm2 = mSolver.binary("#b0010");
		final Term consTerm3 = mSolver.binary("#b0100");

		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("bvshl", consTerm, consTerm2), consTerm3),
				mSolver.term("=", mSolver.term("bvlshr", consTerm, consTerm2), consTerm2),
				mSolver.term("=", mSolver.term("bvshl", mSolver.binary("#b00110011"), mSolver.binary("#b00000010")),
						mSolver.binary("#b11001100")),
				mSolver.term("=", mSolver.term("bvlshr", mSolver.binary("#b00110011"), mSolver.binary("#b00000010")),
						mSolver.binary("#b00001100")));

		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);

	}

	@Test
	public void constBvPatter() {
		mSolver.resetAssertions();
		// final Term consTerm = mSolver.term("(_ bv 4 4)");
		final String[] asd = new String[2];
		asd[0] = "2";
		asd[1] = "1";
		final String[] constindices = new String[1];
		constindices[0] = "4";
		final Term consTerm = mSolver.term("bv3", constindices, null);
		final Term consTerm2 = mSolver.binary("#b0011");
		final Term input = mSolver.term("=", consTerm, consTerm2);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);

	}

	@Test
	public void constRepeat() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input = mSolver.term("=", mSolver.binary("#b1100110011001100"),
				mSolver.term("repeat", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constNAryLogical() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0000"),
						mSolver.term("bvand", mSolver.binary("#b1000"), mSolver.binary("#b1100"),
								mSolver.binary("#b0110"))),
				mSolver.term("=", mSolver.binary("#b1111"), mSolver.term("bvxor", mSolver.binary("#b1000"),
						mSolver.binary("#b0100"), mSolver.binary("#b0011"))));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constSignExtend() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input = mSolver.term("=", mSolver.binary("#b11111100"),
				mSolver.term("sign_extend", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constZeroExtend() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input =
				mSolver.term("and", mSolver.term("=", p8, mSolver.term("concat", mSolver.binary("#b0000"), p4)),
						mSolver.term("=", p8, mSolver.term("zero_extend", indices, null, p4)),
						mSolver.term("=", mSolver.binary("#b00001100"),
								mSolver.term("zero_extend", indices, null, mSolver.binary("#b1100"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constRotateLeft() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "5";
		final Term input = mSolver.term("=", mSolver.binary("#b0110"),
				mSolver.term("rotate_left", indices, null, mSolver.binary("#b0011")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constRotateRight() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "3";
		final Term input = mSolver.term("=", mSolver.binary("#b1001"),
				mSolver.term("rotate_right", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constBvSDIV() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvsdiv", mSolver.binary("#b1100"), mSolver.binary("#b0010")),
				mSolver.binary("#b1110"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void constBvSMOD() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvsmod", mSolver.binary("#b0101"), mSolver.binary("#b0010")),
				mSolver.binary("#b0001"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void selectPropagation() {
		mSolver.resetAssertions();
		final String[] idx = new String[2];
		idx[0] = "5";
		idx[1] = "3";
		final Term consTerm1 = mSolver.binary("#b1111");
		final Term consTerm2 = mSolver.binary("#b0000");
		final Term term1 = mSolver.term("extract", idx, null, mSolver.term("concat", consTerm1, consTerm2));
		final Term input1 = mSolver.term("=", term1, p3);
		mSolver.assertTerm(input1);
		final String[] idx2 = new String[2];
		idx2[0] = "5";
		idx2[1] = "2";
		final String[] idx3 = new String[2];
		idx3[0] = "2";
		idx3[1] = "1";
		final Term term2 =
				mSolver.term("extract", idx3, null, mSolver.term("extract", idx2, null, mSolver.binary("#b0100100")));
		final Term input2 = mSolver.term("=", term2, p2);
		mSolver.assertTerm(input2);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bvultGraphTransitivity() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term input = mSolver.term("and", mSolver.term("bvult", consTerm, q4), mSolver.term("bvult", q2, p2),
				mSolver.term("bvult", p4, consTerm),
				mSolver.term("or", mSolver.term("bvult", q4, p4), mSolver.term("bvult", q4, consTerm)));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isunSat);
	}

	@Test
	public void trivialConflict() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term input = mSolver.term("and", mSolver.term("=", consTerm, q4), mSolver.term("bvult", q4, consTerm));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isunSat);
	}

	@Test
	public void eqConcatMatch() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("concat", y, z), mSolver.term("concat", x, c),
				mSolver.term("concat", a, b));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void eqConcatNoMatch() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("not", mSolver.term("=", mSolver.term("concat", p4, q3), p7)),
				mSolver.term("not", mSolver.term("=", mSolver.term("concat", p2, q2), mSolver.term("concat", p, q3))));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void nonBinaryEqualities() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0001"), mSolver.binary("#b0001"), mSolver.binary("#b0001")),
				mSolver.term("=", mSolver.binary("#b0001"), p4, q4),
				mSolver.term("=", mSolver.term("concat", y, z), mSolver.term("concat", y, z)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void divZero() {
		final Term consTerm15 = mSolver.hexadecimal("#xF");
		final Term consTerm0 = mSolver.binary("#b0000");
		final Term consTerm3 = mSolver.binary("#b0011");
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("and", mSolver.term("=", mSolver.term("bvudiv", consTerm3, consTerm0), consTerm15),
						mSolver.term("=", mSolver.term("bvurem", consTerm15, consTerm0), consTerm15),
						mSolver.term("=", mSolver.term("bvudiv", p4, consTerm0), consTerm15),
						mSolver.term("=", mSolver.term("bvurem", p4, consTerm0), p4));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void divZero2() {
		final Term consTerm0 = mSolver.binary("#b0000");
		final Term consTerm3 = mSolver.binary("#b0011");
		final Term consTerm15 = mSolver.hexadecimal("#xF");
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("and", mSolver.term("=", mSolver.term("bvudiv", consTerm3, consTerm0), consTerm0),
						mSolver.term("=", mSolver.term("bvurem", consTerm3, consTerm0), consTerm15));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bitMaskElimAND() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b1111"), mSolver.term("bvand", p4, mSolver.binary("#b0110"))),
				mSolver.term("=", p4, mSolver.binary("#b0011")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitMaskElimOR() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b1110"), mSolver.term("bvor", p4, mSolver.binary("#b0110"))),
				mSolver.term("=", p4, mSolver.binary("#b0001")),
				mSolver.term("=", mSolver.binary("#b0001"), mSolver.binary("#b0001")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecLearnConflict1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b00")), q2),
				mSolver.term("or", mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b11")), q2),
						mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b01")), q2)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecLearnConflict2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b1000"), p4),
				mSolver.term("or", mSolver.term("not", mSolver.term("=", mSolver.binary("#b1011"), p4)),
						mSolver.term("=", mSolver.binary("#b1001"), p4)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecLearnConflict3() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "1";
		final String[] constindices2 = new String[1];
		constindices2[0] = "2";

		final Term input =
				mSolver.term("not",
						mSolver.term("=",
								mSolver.term("concat", mSolver.term("bv1", constindices, null),
										mSolver.term("bv0", constindices, null)),
								mSolver.term("bv2", constindices2, null)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	// (= (concat (ite (not (= (_ bv0 1) (_ bv1 1))) (_ bv1 1) (_ bv0 1)) (_ bv0 1)) (_ bv2 2))
	@Test
	public void bitVecITE() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "1";
		final String[] constindices2 = new String[1];
		constindices2[0] = "2";

		final Term input = mSolver.term("=", mSolver.term("concat",
				mSolver.term("ite", mSolver.term("not", mSolver.term("=", mSolver.term("bv0", constindices, null), p)),
						mSolver.term("bv1", constindices, null), mSolver.term("bv0", constindices, null)),
				mSolver.term("bv0", constindices, null)), mSolver.term("bv2", constindices2, null));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void cClosureBvult() {
		// x < y::z, ~(x < w), w = y:: z
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", w, mSolver.term("concat", y, z)),
				mSolver.term("not", mSolver.term("bvult", u, w)),
				mSolver.term("bvult", u, mSolver.term("concat", y, z)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void cClosureBvult2() {
		// x < y::z, ~(x < w), w = y:: z
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("bvult", u, mSolver.term("concat", y, z)),
				mSolver.term("=", mSolver.term("concat", y, z), w), mSolver.term("not", mSolver.term("bvult", u, w)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
	}

	@Test
	public void cClosureEqualities() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("concat", y, z), w),
				mSolver.term("not", mSolver.term("=", u, w)), mSolver.term("=", u, mSolver.term("concat", y, z)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bbConcat() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b01"), mSolver.term("concat", p, mSolver.binary("#b1"))),
				mSolver.term("=", p, mSolver.binary("#b1")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bbExtract() {
		mSolver.resetAssertions();
		final String[] indices = new String[2];
		indices[0] = "2";
		indices[1] = "1";
		final String[] indices2 = new String[2];
		indices2[0] = "3";
		indices2[1] = "2";
		final String[] indices3 = new String[2];
		indices3[0] = "2";
		indices3[1] = "0";
		final String[] indices4 = new String[2];
		indices4[0] = "3";
		indices4[1] = "1";
		final Term input = mSolver.term("and", mSolver.term("=", p2, mSolver.term("extract", indices2, null, p4)),
				mSolver.term("=", mSolver.term("extract", indices, null, p4),
						mSolver.term("extract", indices2, null, p4)),
				mSolver.term("=", mSolver.term("extract", indices3, null, p4),
						mSolver.term("extract", indices4, null, p4)));

		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bbBvnand() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvnand", mSolver.binary("#b11110010"), p8),
				mSolver.binary("#b11001101"));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbBvor() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvor", mSolver.binary("#b11000010"), p8), mSolver.binary("#b11110010"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbBvcomp() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvcomp", p4, q4), mSolver.binary("#b1"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbDivSat() {
		final Term consTerm0 = mSolver.binary("#b0");
		final Term consTerm3 = mSolver.binary("#b1");
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("bvudiv", consTerm3, p), consTerm0),
				mSolver.term("=", consTerm3, p));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertTrue(isSat.equals(LBool.UNSAT) || isSat.equals(LBool.UNKNOWN));
	}

	@Test
	public void bbDivUNSat() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvudiv", mSolver.binary("#b100"), p3), mSolver.binary("#b010")),
				mSolver.term("=", mSolver.binary("#b001"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertTrue(isSat.equals(LBool.UNSAT) || isSat.equals(LBool.UNKNOWN));
	}

	@Test
	public void bbRemSat() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvurem", mSolver.binary("#b101"), p3), mSolver.binary("#b001")),
				mSolver.term("=", mSolver.binary("#b010"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertTrue(isSat.equals(LBool.SAT) || isSat.equals(LBool.UNKNOWN));
	}

	@Test
	public void bbRemUNSat() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvurem", mSolver.binary("#b100"), p3), mSolver.binary("#b001")),
				mSolver.term("=", mSolver.binary("#b010"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertTrue(isSat.equals(LBool.UNSAT) || isSat.equals(LBool.UNKNOWN));
	}

	@Test
	public void bbRemUNSat2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvurem", mSolver.binary("#b011"), p3), mSolver.binary("#b001")),
				mSolver.term("=", p3, mSolver.binary("#b011")));

		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertTrue(isSat.equals(LBool.UNSAT) || isSat.equals(LBool.UNKNOWN));
	}

	@Test
	public void bbLeftShiftSAT1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvshl", q3, p3), mSolver.binary("#b100"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b10000000"),
				mSolver.term("bvshl", p8, mSolver.binary("#b00000111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftSAT3() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b000"), mSolver.term("bvshl", p3, mSolver.binary("#b111"))),
				mSolver.term("=", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftSAT4() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b00"), mSolver.term("bvshl", p2, mSolver.binary("#b00"))),
				mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftUNSAT1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b000"), mSolver.term("bvshl", p3, mSolver.binary("#b001"))),
				mSolver.term("=", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftUNSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b10"), mSolver.term("bvshl", p2, mSolver.binary("#b01"))),
				mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbLeftShiftUNSAT3() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b00000001"),
				mSolver.term("bvshl", p8, mSolver.binary("#b00001000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftSAT1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0001"), mSolver.term("bvlshr", p4, mSolver.binary("#b0011"))),
				mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0100"), mSolver.term("bvlshr", p4, mSolver.binary("#b0001"))),
				mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftSAT3() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0000"), mSolver.term("bvlshr", p4, mSolver.binary("#b1111"))),
				mSolver.term("=", p4, mSolver.binary("#b1111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftUNSAT1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0010"), mSolver.term("bvlshr", p4, mSolver.binary("#b0011"))),
				mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftUNSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0010"), mSolver.term("bvlshr", p4, mSolver.binary("#b0010"))),
				mSolver.term("=", p4, mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftUNSAT3() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0000"), mSolver.term("bvlshr", p4, mSolver.binary("#b0001"))),
				mSolver.term("=", p4, mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbRightShiftUNSAT4() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0000"), mSolver.term("bvlshr", p4, mSolver.binary("#b0000"))),
				mSolver.term("=", p4, mSolver.binary("#b1111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbAddSAT1() {
		mSolver.resetAssertions();
		final Term input =

				mSolver.term("and", mSolver.term("not", mSolver.term("=", mSolver.binary("#b111"), q3)),
						mSolver.term("=", mSolver.binary("#b111"), mSolver.term("bvadd", mSolver.binary("#b111"),
								mSolver.term("bvadd", mSolver.binary("#b001"), q3))))

		;
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbAddSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b00"), mSolver.term("bvadd", p2, mSolver.binary("#b00"))),
				mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbAddSAT3() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b11"), mSolver.term("bvadd", p2, mSolver.binary("#b01")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbAddSAT4() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.binary("#b100"), mSolver.term("bvadd", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbAddSAT5() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b10"), p2),
				mSolver.term("=", mSolver.binary("#b11"), mSolver.term("bvadd", p2, mSolver.binary("#b01"))));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void congruenceVsRanged() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b11111111"), mSolver.term("bvadd",
				mSolver.term("bvmul", mSolver.term("bvadd", p8, q8), mSolver.binary("#b00011110")), q8));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbAddUNSAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b10"), mSolver.term("bvadd", p2, mSolver.binary("#b10"))),

				mSolver.term("=", mSolver.binary("#b11"), mSolver.term("bvadd", p2, mSolver.binary("#b01"))));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bbMulSAT() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvmul", p3, mSolver.binary("#b010")), mSolver.binary("#b100"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbMulSATZero() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvmul", p3, mSolver.binary("#b000")), mSolver.binary("#b000"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbMulUNSAT1() {
		mSolver.resetAssertions();
		final Sort bv4 = mSolver.getTheory().getSort("BitVec", new String[] { "4" });
		mSolver.defineFun("fun", new TermVariable[0], bv4, mSolver.term("bvand", p4, mSolver.binary("#b0010")));

		final Term input = mSolver.term("=", mSolver.term("bvadd", p4, mSolver.term("fun")), mSolver.binary("#b1001"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbMulUNSAT1inlined() {
		mSolver.resetAssertions();
		final Sort bv4 = mSolver.getTheory().getSort("BitVec", new String[] { "4" });

		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvadd", p4, mSolver.term("bvand", p4, mSolver.binary("#b0010"))),
						mSolver.binary("#b1001")),

				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b1001"))),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b0111"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbMulUNSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvmul", p4, mSolver.binary("#b0010")), mSolver.binary("#b0100")),
				mSolver.term("=", p4, mSolver.binary("#b0000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbBvneg() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.term("bvneg", p4), mSolver.binary("#b1111")),
				mSolver.term("=", p4, mSolver.binary("#b0001")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbNotAtom() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", p2, mSolver.binary("#b11")),
				mSolver.term("not", mSolver.term("=", p2, mSolver.binary("#b11"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbBVULTAtom() {
		mSolver.resetAssertions();
		// p4 = 0000
		final Term input = mSolver.term("and", mSolver.term("bvult", p4, mSolver.binary("#b0011")),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b0001"))),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b0010"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbBVULTAtom2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("bvult", mSolver.binary("#b0111"), p4),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b1000"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bbSubSAT1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvsub", mSolver.binary("#b0111"), p4), mSolver.binary("#b0001")),
				mSolver.term("=", p4, mSolver.binary("#b0110")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void benchmarkBug() {
		mSolver.resetAssertions();

		final String[] indices = new String[1];
		indices[0] = "3";
		final String[] indices2 = new String[1];
		indices2[0] = "2";
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0011"),
						mSolver.term("rotate_left", indices, null, mSolver.term("rotate_left", indices2, null, p4))),
				mSolver.term("=", mSolver.binary("#b1001"), p4));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void benchmarkBug2() {
		mSolver.resetAssertions();

		final String[] indices = new String[1];
		indices[0] = "4";

		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b1011"), p4),
				mSolver.term("=", p4, mSolver.term("rotate_left", indices, null, p4)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void benchmarkBug4() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("and", mSolver.term("=", mSolver.term("bvand", p4, mSolver.term("bvnot", p4)), q4),
						mSolver.term("not", mSolver.term("=", mSolver.binary("#b0000"), q4)));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	// (= (bvand #b00110011 (bvshl (_ bv1 8) ((_ zero_extend 5) (_ bv1 3)))) (_ bv0 8))
	@Test
	public void benchmarkBug44() {
		mSolver.resetAssertions();

		final String[] indices = new String[1];
		indices[0] = "5";

		final Term input = mSolver.term("=",
				mSolver.term("bvand", mSolver.binary("#b10110011"),
						mSolver.term("bvshl", mSolver.binary("#b00000001"),
								mSolver.term("zero_extend", indices, null, mSolver.binary("#b111")))),
				mSolver.binary("#b00000000"));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void benchmarkBug5Rem() {
		mSolver.resetAssertions();

		final String[] indices = new String[1];
		indices[0] = "5";

		final Term input =

				mSolver.term("not", mSolver.term("=", mSolver.binary("#b00000100"),
						mSolver.term("bvurem", mSolver.binary("#b00000100"), mSolver.binary("#b00000111"))));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void benchmarkBug6Rem() {
		mSolver.resetAssertions();

		final String[] indices = new String[1];
		indices[0] = "5";

		final Term input =

				mSolver.term("=", mSolver.binary("#b00000110"),
						mSolver.term("bvurem", mSolver.binary("#b00000100"), mSolver.binary("#b00000111")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

}