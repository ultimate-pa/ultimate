package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;

/**
 * 
 * @author Jan Hättig
 *
 */
public class CompoundState implements IAbstractState<CompoundState> {
	private final List<IAbstractState<?>> mStates;

	/**
	 * Constructor
	 * 
	 * @param initialStates
	 */
	public CompoundState(List<IAbstractState<?>> initialStates) {
		mStates = initialStates;
	}

	/**
	 * Copy constructor. Does not copy the internal states
	 * 
	 * @param original
	 */
	public CompoundState(CompoundState original) {
		mStates = new ArrayList<IAbstractState<?>>(original.mStates);
	}

	/**
	 * Returns the state of a domain with the given index
	 * 
	 * @param index
	 * @return
	 */
	public IAbstractState<?> getState(int index) {
		return mStates.get(index);
	}

	/**
	 * Sets the state of a domain, indexed
	 * 
	 * @param index
	 * @param newState
	 */
	public void setState(int index, IAbstractState<?> newState) {
		mStates.set(index, newState);
	}

	@Override
	public boolean isSuperOrEqual(IAbstractState<?> state) {
		if (state.isBottom()) {
			return true;
		}

		if (isBottom()) {
			return false;
		}

		if (!(state instanceof CompoundState)) {
			return false;
		}
		final CompoundState cstate = (CompoundState) state;
		for (int i = 0; i < mStates.size(); i++) {
			if (!mStates.get(i).isSuperOrEqual(cstate.getConcrete().getState(i))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean hasVariable(AbstractVariable variable) {
		for (IAbstractState<?> state : mStates) {
			if (state.hasVariable(variable)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void declareVariable(TypedAbstractVariable variable) {
		for (IAbstractState<?> state : mStates) {
			state.declareVariable(variable);
		}
	}

	@Override
	public TypedAbstractVariable getTypedVariable(AbstractVariable variable) {
		for (IAbstractState<?> state : mStates) {
			if (state.hasVariable(variable)) {
				return state.getTypedVariable(variable);
			}
		}

		return null;
	}

	@Override
	public void removeVariable(AbstractVariable variable) {
		for (IAbstractState<?> state : mStates) {
			state.removeVariable(variable);
		}
	}

	@Override
	public IAbstractState<CompoundState> copy() {
		List<IAbstractState<?>> copies = new ArrayList<IAbstractState<?>>();
		for (IAbstractState<?> state : mStates) {
			copies.add(state.copy());
		}
		return new CompoundState(copies);
	}

	@Override
	public boolean isBottom() {
		for (IAbstractState<?> state : mStates) {
			if (state.isBottom()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Refine all states on each other
	 */
	public void refine(List<IRefinement> refs) {
		for (IRefinement ref : refs) {
			for (IAbstractState<?> s1 : mStates) {
				for (IAbstractState<?> s2 : mStates) {
					if (s1 == s2) {
						// only one way, no mirror
						continue;
					}
					ref.refine(s1, s2);
				}
			}
		}
	}

	@Override
	public CompoundState getConcrete() {
		return this;
	}

	public int getNofStates() {
		return mStates.size();
	}

	@Override
	public String toString() {
		String s = "GC(";
		String comma = "";
		for (IAbstractState<?> state : mStates) {
			s += comma + state.toString();
			comma = " && ";
		}
		return s + ")";
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}

		Term acc = script.term("true");
		for (final IAbstractState<?> state : mStates) {
			acc = Util.and(script, acc, state.getTerm(script, bpl2smt));
		}
		return acc;
	}
}
