package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISemanticReducerFactory;

public class InterpolantTreeAutomatonBU<LETTER extends IRankedLetter, STATE> extends TreeAutomatonBU<LETTER, STATE> {

	private final ISemanticReducerFactory<STATE, LETTER> mReducer;


	public <SF extends ISemanticReducerFactory<STATE, LETTER>> InterpolantTreeAutomatonBU(final SF fac) {
		super(fac);
		mReducer = fac;
	}

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final List<STATE> source) {
		return mReducer.reduceRules(super.getSuccessors(source));
	}

	@Override
	public Iterable<STATE> getSuccessors(final List<STATE> source, final LETTER letter) {
	//	return mReducer.getOptimalDestination(null, letter, null);
		return mReducer.filter(super.getSuccessors(source, letter));
	}

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final LETTER letter) {
		return mReducer.reduceRules(super.getSuccessors(letter));
	}

}
