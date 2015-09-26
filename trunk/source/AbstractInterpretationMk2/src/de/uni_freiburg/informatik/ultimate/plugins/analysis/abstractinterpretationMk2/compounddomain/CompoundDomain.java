package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

/**
 * Unites several domains to be one And
 * 
 * @author Jan Hättig
 *
 */
@SuppressWarnings({ "rawtypes", "unchecked" })
public class CompoundDomain implements IAbstractDomain<CompoundState> {
	private static String s_domainID = "COMPOUND";

	private final List<IAbstractDomain> mDomains;

	private final List<IRefinement> mRefinements;

	/*
	 * The merge operator which is used for this domain.
	 */
	private IAbstractMergeOperator<CompoundState> mMergeOperator;
	/**
	 * The widening operator which is used for this domain.
	 */
	private IAbstractWideningOperator<CompoundState> mWideningOperator;

	public CompoundDomain(List<IAbstractDomain> domains,
			List<IRefinement> refinements) {
		mDomains = domains;
		mRefinements = refinements;
	}

	public IAbstractDomain getDomain(int i) {
		return mDomains.get(i);
	}

	@Override
	public void setMergeOperator(
			IAbstractMergeOperator<CompoundState> mergeOperator) {
		mMergeOperator = mergeOperator;
	}

	@Override
	public void setWideningOperator(
			IAbstractWideningOperator<CompoundState> wideningOperator) {
		mWideningOperator = wideningOperator;
	}

	@Override
	public IAbstractMergeOperator<CompoundState> getMergeOperator() {
		return mMergeOperator;
	}

	@Override
	public IAbstractWideningOperator<CompoundState> getWideningOperator() {
		return mWideningOperator;
	}

	@Override
	public IAbstractState<CompoundState> createState() {
		List<IAbstractState> states = new ArrayList<IAbstractState>();
		for (IAbstractDomain domain : mDomains) {
			states.add(domain.createState());
		}
		return new CompoundState(states);
	}

	@Override
	public IAbstractState<CompoundState> applyExpression(
			IAbstractState<CompoundState> state, TypedAbstractVariable target,
			Expression exp) {
		for (int i = 0; i < mDomains.size(); i++) {
			// the instances are manipulated
			IAbstractState newState = mDomains.get(i).applyExpression(
					(IAbstractState) state.getConcrete().getState(i), target,
					exp);
			state.getConcrete().setState(i, newState);
		}
		// refine after each expression
		state.getConcrete().refine(mRefinements);
		// the reference is not changed (does not need to)
		return (IAbstractState<CompoundState>) state;
	}

	@Override
	public IAbstractState<CompoundState> applyHavoc(
			IAbstractState<CompoundState> state, TypedAbstractVariable target) {
		for (int i = 0; i < mDomains.size(); i++) {
			// the instances are manipulated
			IAbstractState newState = mDomains.get(i).applyHavoc(
					(IAbstractState) state.getConcrete().getState(i), target);
			state.getConcrete().setState(i, newState);
		}
		// the reference is not changed (does not need to)
		return (IAbstractState<CompoundState>) state;
	}

	@Override
	public List<IAbstractState<CompoundState>> applyAssume(
			IAbstractState<CompoundState> state, Expression exp) {
		List<IAbstractState<CompoundState>> newCompoundStates = new ArrayList<IAbstractState<CompoundState>>();

		// [domainNum][state]
		List<List<IAbstractState>> statesFromDomains = new ArrayList<List<IAbstractState>>();

		for (int i = 0; i < mDomains.size(); i++) {
			List<IAbstractState> statesFromDomain = mDomains.get(i)
					.applyAssume(
							(IAbstractState) state.getConcrete().getState(i),
							exp);
			// no states from one domain => bottom
			if (statesFromDomain.isEmpty()) {
				return new ArrayList<IAbstractState<CompoundState>>();
			}
			statesFromDomains.add(statesFromDomain);
		}

		// build the cross product
		// dIndex stores which thing we are building start
		// with 0,...,0 end with max, ..., max
		int[] digits = new int[mDomains.size()];
		int index = 0;
		while (index < digits.length) {
			// -- build the state --
			List<IAbstractState> statesForActual = new ArrayList<IAbstractState>();
			boolean bottom = false;
			for (int i = 0; i < digits.length; i++) {
				IAbstractState actual = statesFromDomains.get(i).get(digits[i]);
				if (actual.isBottom()) {
					// do not add corss products containing bottom
					bottom = true;
					break;
				}
				statesForActual.add(actual);
			}
			if (!bottom) {
				newCompoundStates.add(new CompoundState(statesForActual));
			}

			// -- increase digits by one --
			index = 0;
			while (index < digits.length) {
				digits[index]++;
				if (digits[index] < statesFromDomains.get(index).size()) {
					break;
				} else {
					digits[index] = 0;
					index++;
				}
			}
		}

		return newCompoundStates;
	}

	@Override
	public void applyExpressionScoped(
			IAbstractState<CompoundState> targetState,
			IAbstractState<CompoundState> oldState,
			List<TypedAbstractVariable> targets, List<Expression> arguments) {
		for (int i = 0; i < mDomains.size(); i++) {
			// the instances are manipulated
			mDomains.get(i).applyExpressionScoped(
					(IAbstractState) targetState.getConcrete().getState(i),
					(IAbstractState) oldState.getConcrete().getState(i),
					targets, arguments);
		}
		// refine after changes
		// targetState.getConcrete().refine(mRefinements);
	}

	@Override
	public boolean checkAssert(IAbstractState<CompoundState> state,
			Expression exp) {
		for (int i = 0; i < mDomains.size(); i++) {
			// it is sufficient if one abstractin tells us that the assert holds
			if (mDomains.get(i).checkAssert(
					(IAbstractState) state.getConcrete().getState(i), exp)) {
				return true;
			}
		}
		// if no one witnesses innocence
		return false;
	}

	public static String getDomainID() {
		return s_domainID;
	}
}
