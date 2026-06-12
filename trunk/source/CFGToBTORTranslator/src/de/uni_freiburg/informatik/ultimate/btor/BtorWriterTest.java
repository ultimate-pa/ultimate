package de.uni_freiburg.informatik.ultimate.btor;

import java.io.IOException;
import java.io.OutputStreamWriter;

import de.uni_freiburg.informatik.ultimate.btor.expression.AddExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ConstdExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ITEExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.InitExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NeqExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NextExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SdivExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SltExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SremExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.StateExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SubExpression;

public class BtorWriterTest {

	public static void main(final String[] args) throws IOException {
		// final BtorExpression one = new BtorExpression(32, BtorExpressionType.ONE, new ArrayList<>());
		final BtorScript script = new BtorScript();
//		final OneExpression one = script.createOneExpression(new BtorSort(32));
//		final StateExpression state = script.createStateExpression(new BtorSort(32), "aa");
//		final InitExpression init = script.createInitExpression(state, one);
//		final ConstdExpression constd = script.createConstdExpression(new BtorSort(32), 10);
//		final ConstdExpression constd2 = script.createConstdExpression(new BtorSort(32), 10);
//		final EqExpression equ = script.createBinaryExpression(EqExpression.class, constd, one);
//		final EqExpression equ2 = script.createBinaryExpression(EqExpression.class, constd, constd2);
//		final NotExpression not = script.createUnaryExpression(NotExpression.class, equ);
//		final NotExpression not2 = script.createUnaryExpression(NotExpression.class, equ);

		final BtorExpression zero = script.createZeroExpression(new BtorSort(32));
		final BtorExpression one = script.createOneExpression(new BtorSort(32));
		final StateExpression divRes = script.createStateExpression(new BtorSort(32), "divRes");
		final StateExpression modRes = script.createStateExpression(new BtorSort(32), "modRes");
		final ConstdExpression lhs = script.createConstdExpression(new BtorSort(32), -32);
		final ConstdExpression rhs = script.createConstdExpression(new BtorSort(32), 13);
		final ConstdExpression expectedDiv = script.createConstdExpression(new BtorSort(32), -2);
		final ConstdExpression expectedMod = script.createConstdExpression(new BtorSort(32), 6);
		final BtorExpression mod = script.createBinaryExpression(SremExpression.class, lhs, rhs);
		final BtorExpression div = script.createBinaryExpression(SdivExpression.class, lhs, rhs);
		final BtorExpression divInc = script.createBinaryExpression(AddExpression.class, div, one);
		final BtorExpression divDec = script.createBinaryExpression(SubExpression.class, div, one);
		final BtorExpression rhsSign = script.createBinaryExpression(SltExpression.class, rhs, zero);
		final BtorExpression divAdjust = script.createTernaryExpression(ITEExpression.class, rhsSign, divInc, divDec);

		final BtorExpression modAdd = script.createBinaryExpression(SubExpression.class, mod, rhs);
		final BtorExpression modSub = script.createBinaryExpression(AddExpression.class, mod, rhs);

		final BtorExpression modInc = script.createTernaryExpression(ITEExpression.class, rhsSign, modAdd, modSub);

		final BtorExpression slt = script.createBinaryExpression(SltExpression.class, mod, zero);
		final BtorExpression resultDiv = script.createTernaryExpression(ITEExpression.class, slt, divAdjust, div);
		final BtorExpression resultMod = script.createTernaryExpression(ITEExpression.class, slt, modInc, mod);
		final InitExpression init1 = script.createInitExpression(divRes, resultDiv);
		final InitExpression init2 = script.createInitExpression(modRes, resultMod);
		final NextExpression next1 = script.createNextExpression(divRes, divRes);
		final NextExpression next2 = script.createNextExpression(modRes, modRes);

		final BtorExpression neq = script.createBinaryExpression(NeqExpression.class, divRes, expectedDiv);
		final BtorExpression neq2 = script.createBinaryExpression(NeqExpression.class, modRes, expectedMod);
		final BtorExpression bad = script.createBadExpression(neq);
		final BtorExpression bad2 = script.createBadExpression(neq2);

		script.dumpScript(new OutputStreamWriter(System.out));
		// System.out.println(result);
//		System.out.println(not.equals(not2));
//		System.out.println(not2.equals(not));

	}

}