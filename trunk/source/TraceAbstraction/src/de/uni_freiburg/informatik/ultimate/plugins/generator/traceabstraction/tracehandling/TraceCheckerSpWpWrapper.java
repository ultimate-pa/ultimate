package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * Wraps a {@link TraceCheckerSpWp} because it has two interpolant sequences.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TraceCheckerSpWpWrapper implements IInterpolantGenerator {
	/**
	 * Possible mode of obtaining interpolants.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private enum InterpolationMode {
		/**
		 * Forward interpolants.
		 */
		FORWARD,
		/**
		 * Backward interpolants.
		 */
		BACKWARD,
		/**
		 * No more interpolants.
		 */
		FINISHED
	}
	
	private static final String NO_MORE_INTERPOLANTS_AVAILABLE_IN_MODE = "No more interpolants available in mode ";
	private static final String UNKNOWN_MODE = "Unknown mode ";
	
	private final TraceCheckerSpWp mTraceCheckerSpWp;
	private TraceCheckerSpWpWrapper.InterpolationMode mMode;
	
	/**
	 * @param traceCheckerSpWp
	 *            The trace checker that is wrapped.
	 */
	public TraceCheckerSpWpWrapper(final TraceCheckerSpWp traceCheckerSpWp) {
		mTraceCheckerSpWp = traceCheckerSpWp;
		mMode = InterpolationMode.FORWARD;
	}
	
	/**
	 * @return {@code true} iff there are more interpolant sequences available.
	 */
	public boolean hasNext() {
		return mMode != InterpolationMode.FINISHED;
	}
	
	/**
	 * Changes the direction.<br>
	 * Throws a {@link NoSuchElementException} if there is no next combination; use {@link #hasNext()} to
	 * check this.
	 */
	public void next() {
		switch (mMode) {
			case FORWARD:
				mMode = InterpolationMode.BACKWARD;
				break;
			case BACKWARD:
				mMode = InterpolationMode.FINISHED;
				break;
			case FINISHED:
				throw new NoSuchElementException();
			default:
				throw new UnsupportedOperationException(UNKNOWN_MODE + mMode);
		}
	}
	
	@Override
	public Word<? extends IAction> getTrace() {
		return mTraceCheckerSpWp.getTrace();
	}
	
	@Override
	public IPredicate getPrecondition() {
		return mTraceCheckerSpWp.getPrecondition();
	}
	
	@Override
	public IPredicate getPostcondition() {
		return mTraceCheckerSpWp.getPostcondition();
	}
	
	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return mTraceCheckerSpWp.getPendingContexts();
	}
	
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mTraceCheckerSpWp.getPredicateUnifier();
	}
	
	@Override
	public IPredicate[] getInterpolants() {
		List<IPredicate> interpolants;
		switch (mMode) {
			case FORWARD:
				interpolants = mTraceCheckerSpWp.getForwardPredicates();
				break;
			case BACKWARD:
				interpolants = mTraceCheckerSpWp.getBackwardPredicates();
				break;
			case FINISHED:
				throw new UnsupportedOperationException(NO_MORE_INTERPOLANTS_AVAILABLE_IN_MODE + mMode);
			default:
				throw new UnsupportedOperationException(UNKNOWN_MODE + mMode);
		}
		return interpolants.toArray(new IPredicate[interpolants.size()]);
	}
	
	@Override
	public InterpolantsPreconditionPostcondition getIpp() {
		switch (mMode) {
			case FORWARD:
				return mTraceCheckerSpWp.getForwardIpp();
			case BACKWARD:
				return mTraceCheckerSpWp.getBackwardIpp();
			case FINISHED:
				throw new UnsupportedOperationException(NO_MORE_INTERPOLANTS_AVAILABLE_IN_MODE + mMode);
			default:
				throw new UnsupportedOperationException(UNKNOWN_MODE + mMode);
		}
	}
	
	@Override
	public boolean isPerfectSequence() {
		switch (mMode) {
			case FORWARD:
			case BACKWARD:
				// TODO does the class do the right thing?
				return mTraceCheckerSpWp.isPerfectSequence();
			case FINISHED:
				throw new UnsupportedOperationException(NO_MORE_INTERPOLANTS_AVAILABLE_IN_MODE + mMode);
			default:
				throw new UnsupportedOperationException(UNKNOWN_MODE + mMode);
		}
	}
}
