package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Arrays;

public class BtorWriterTest {

	public static void main(final String[] args) throws IOException {
		final BtorExpression one = new BtorExpression(32, BtorExpressionType.ONE, new ArrayList<>());
		final BtorExpression state = new BtorExpression(32, BtorExpressionType.STATE, new ArrayList<>());
		final BtorExpression init = new BtorExpression(32, BtorExpressionType.INIT, Arrays.asList(state, one));

		final BtorScript script = new BtorScript(Arrays.asList(init), Arrays.asList(32));
		script.dumpScript(new OutputStreamWriter(System.out));

	}

}
