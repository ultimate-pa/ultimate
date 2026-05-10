package de.uni_freiburg.informatik.ultimate.btor;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.btor.expression.ConstdExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.EqExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.InitExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NotExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.OneExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.StateExpression;

public class BtorWriterTest {

	public static void main(final String[] args) throws IOException {
		// final BtorExpression one = new BtorExpression(32, BtorExpressionType.ONE, new ArrayList<>());
		final BtorScript script = new BtorScript(Arrays.asList(new BtorSort(32), new BtorSort(1)));
		final OneExpression one = script.createOneExpression(new BtorSort(32));
		final StateExpression state = script.createStateExpression(new BtorSort(32), "aa");
		final InitExpression init = script.createInitExpression(state, one);
		final ConstdExpression constd = script.createConstdExpression(new BtorSort(32), 10);
		final ConstdExpression constd2 = script.createConstdExpression(new BtorSort(32), 10);
		final EqExpression equ = script.createBinaryExpression(EqExpression.class, constd, one);
		final EqExpression equ2 = script.createBinaryExpression(EqExpression.class, constd, constd2);
		final NotExpression not = script.createUnaryExpression(NotExpression.class, equ);
		final NotExpression not2 = script.createUnaryExpression(NotExpression.class, equ);

		script.dumpScript(new OutputStreamWriter(System.out));
		System.out.println(not.equals(not2));
		System.out.println(not2.equals(not));

	}

}
