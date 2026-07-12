package de.uni_freiburg.informatik.ultimate.btor;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.btor.expression.BadExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ConstdExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ConstraintExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.InitExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.InputExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NextExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.OneExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SextExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.SliceExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.StateExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.TernaryExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.UextExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ZeroExpression;

public class BtorScript {

	private int currentLine;
	private final HashMap<BtorSort, Integer> sortMap;
	private final StringBuffer text;
	private boolean textExists;

	private final HashMap<BtorExpression, BtorExpression> expressionSet;

	public BtorScript() {
		sortMap = new HashMap<>();
		currentLine = 1;
		text = new StringBuffer();
		textExists = false;
		expressionSet = new HashMap<>();
	}

	public OneExpression createOneExpression(final BtorSort sort) {
		final OneExpression candidate = new OneExpression(sort);
		if (expressionSet.containsKey(candidate)) {
			return (OneExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public ZeroExpression createZeroExpression(final BtorSort sort) {
		final ZeroExpression candidate = new ZeroExpression(sort);
		if (expressionSet.containsKey(candidate)) {
			return (ZeroExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public SextExpression createSextExpression(final BtorExpression child, final int extendBy) {
		final SextExpression candidate = new SextExpression(child, extendBy);
		if (expressionSet.containsKey(candidate)) {
			return (SextExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public UextExpression createUextExpression(final BtorExpression child, final int extendBy) {
		final UextExpression candidate = new UextExpression(child, extendBy);
		if (expressionSet.containsKey(candidate)) {
			return (UextExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public SliceExpression createSliceExpression(final BtorExpression child, final int upper, final int lower) {
		final SliceExpression candidate = new SliceExpression(child, upper, lower);
		if (expressionSet.containsKey(candidate)) {
			return (SliceExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public BadExpression createBadExpression(final BtorExpression bad) {
		final BadExpression candidate = new BadExpression(bad);
		if (expressionSet.containsKey(candidate)) {
			return (BadExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public ConstdExpression createConstdExpression(final BtorSort sort, final long constant) {
		final ConstdExpression candidate = new ConstdExpression(sort, constant);
		if (expressionSet.containsKey(candidate)) {
			return (ConstdExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public ConstraintExpression createConstraintExpression(final BtorExpression constraint) {
		final ConstraintExpression candidate = new ConstraintExpression(constraint);
		if (expressionSet.containsKey(candidate)) {
			return (ConstraintExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public InitExpression createInitExpression(final StateExpression state, final BtorExpression initVal) {
		final InitExpression candidate = new InitExpression(state, initVal);
		if (expressionSet.containsKey(candidate)) {
			return (InitExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public InputExpression createInputExpression(final BtorSort sort, final String name) {
		final InputExpression candidate = new InputExpression(sort, name);
		if (expressionSet.containsKey(candidate)) {
			return (InputExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public NextExpression createNextExpression(final StateExpression state, final BtorExpression nextVal) {
		final NextExpression candidate = new NextExpression(state, nextVal);
		if (expressionSet.containsKey(candidate)) {
			return (NextExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public StateExpression createStateExpression(final BtorSort sort, final String name) {
		final StateExpression candidate = new StateExpression(sort, name);
		if (expressionSet.containsKey(candidate)) {
			return (StateExpression) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public <T extends UnaryExpression> T createUnaryExpression(final Class<T> cls, final BtorExpression child) {
		T candidate = null;
		try {
			candidate = cls.getConstructor(BtorExpression.class).newInstance(child);
		} catch (final Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (candidate == null) {
			throw new UnsupportedOperationException("No");
		}
		if (expressionSet.containsKey(candidate)) {
			return (T) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public <T extends BinaryExpression> T createBinaryExpression(final Class<T> cls, final BtorExpression left,
			final BtorExpression right) {
		T candidate = null;
		try {
			candidate = cls.getConstructor(BtorExpression.class, BtorExpression.class).newInstance(left, right);
		} catch (final Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (candidate == null) {
			throw new UnsupportedOperationException("No");
		}
		if (expressionSet.containsKey(candidate)) {
			return (T) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public <T extends TernaryExpression> T createTernaryExpression(final Class<T> cls, final BtorExpression first,
			final BtorExpression second, final BtorExpression third) {
		T candidate = null;
		try {
			candidate = cls.getConstructor(BtorExpression.class, BtorExpression.class, BtorExpression.class)
					.newInstance(first, second, third);
		} catch (final Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (candidate == null) {
			throw new UnsupportedOperationException("No");
		}
		if (expressionSet.containsKey(candidate)) {
			return (T) expressionSet.get(candidate);
		} else {
			expressionSet.put(candidate, candidate);
			return candidate;
		}
	}

	public Set<BtorSort> getRequiredBtorSorts() {
		final Set<BtorSort> sorts = new HashSet<>();
		for (final BtorExpression expression : expressionSet.keySet()) {
			sorts.add(expression.getSort());
		}
		return sorts;
	}

	private void dumpExpressions(final OutputStreamWriter textStreamWriter, final Deque<BtorExpression> worklist)
			throws IOException {
		final int maxDepth = 30;
		while (!worklist.isEmpty()) {
			final BtorExpression expression = worklist.pop();
			try {
				currentLine = expression.dumpExpression(currentLine, textStreamWriter, sortMap, maxDepth);

			} catch (final MaxDepthException e) {
				worklist.addLast(expression);
				currentLine = e.currentLine;
			}
		}
	}

	public void dumpScript(final OutputStreamWriter writer) throws IOException {
		if (textExists) {
			writer.write(text.toString());
			writer.flush();
			return;
		}
		final ByteArrayOutputStream textStream = new ByteArrayOutputStream();
		final OutputStreamWriter textStreamWriter = new OutputStreamWriter(textStream);

		final Deque<BtorSort> sortWorklist = new ArrayDeque<>(getRequiredBtorSorts());
		while (!sortWorklist.isEmpty()) {
			final BtorSort sort = sortWorklist.pop();
			if (sort.isArray()) {
				final BtorSort keySort = sort.keySort;
				final BtorSort valueSort = sort.valueSort;
				int keySid = 0;
				int valueSid = 0;
				if (valueSort.isArray()) {
					final int i = 1 + 1;
				}
				try {
					keySid = sortMap.get(keySort);
					valueSid = sortMap.get(valueSort);
				} catch (final NullPointerException e) {
					sortWorklist.addLast(sort);
					continue;
				}

				textStreamWriter.write(String.valueOf(currentLine) + " sort array " + String.valueOf(keySid) + " "
						+ String.valueOf(valueSid) + "\n");
			} else {
				textStreamWriter
						.write(String.valueOf(currentLine) + " sort bitvec " + String.valueOf(sort.size) + "\n");
			}

			sortMap.put(sort, currentLine);
			currentLine++;
			textStreamWriter.flush();
		}

		final ArrayDeque<BtorExpression> initExpressionWorklist = new ArrayDeque<>();
		final ArrayDeque<BtorExpression> expressionWorklist = new ArrayDeque<>();

		for (final BtorExpression expression : expressionSet.keySet()) {
			if (expression instanceof InitExpression) {
				initExpressionWorklist.push(expression);
			} else {
				expressionWorklist.push(expression);
			}
		}

		dumpExpressions(textStreamWriter, initExpressionWorklist);
		dumpExpressions(textStreamWriter, expressionWorklist);

		textStreamWriter.flush();
		text.append(textStream.toString());
		writer.write(text.toString());
		writer.flush();
		textExists = true;
	}
}
