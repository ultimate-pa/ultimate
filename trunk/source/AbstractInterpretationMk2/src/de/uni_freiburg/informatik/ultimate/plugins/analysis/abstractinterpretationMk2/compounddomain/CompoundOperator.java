package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

@SuppressWarnings({ "rawtypes", "unchecked" })
public class CompoundOperator implements
		IAbstractWideningOperator<CompoundState>,
		IAbstractMergeOperator<CompoundState> {
	private static final String s_operatorID = "COMPOUND_OPERATORS";

	protected final List<IAbstractOperator> mOperators;

	public CompoundOperator(List<IAbstractOperator> operators) {
		mOperators = operators;
	}

	@Override
	public IAbstractState<CompoundState> apply(IAbstractState<CompoundState> a,
			IAbstractState<CompoundState> b) {
		if (a.getConcrete().getNofStates() != mOperators.size()
				|| b.getConcrete().getNofStates() != mOperators.size()) {
			throw new RuntimeException();
		}

		IAbstractState<CompoundState> result = new CompoundState(
				a.getConcrete());
		for (int i = 0; i < mOperators.size(); i++) {
			result.getConcrete().setState(
					i,
					mOperators.get(i).apply(a.getConcrete().getState(i),
							b.getConcrete().getState(i)));
		}
		return result;
	}

	public static String getOperatorID() {
		return s_operatorID;
	}

}
