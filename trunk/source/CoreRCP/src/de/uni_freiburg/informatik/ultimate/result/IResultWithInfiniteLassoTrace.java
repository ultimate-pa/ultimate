package de.uni_freiburg.informatik.ultimate.result;

/**
 * {@link IResultWithInfiniteLassoTrace} describes results that contain a
 * infinite trace that consists of a finite prefix called the stem, and an
 * infinite but periodic suffix called the lasso.
 * 
 * One can imagine both, the stem and the lasso, as a finite sequence of
 * statements, where the sequence of statements of the lasso repeat themselves
 * infinitely often in the order described by said sequence.
 * 
 * Both, the stem and the lasso, are represented by a {@link IProgramExecution},
 * which consists of a sequence of trace elements of type TE, and which may
 * contain program states, which are described by expressions of type E.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
public interface IResultWithInfiniteLassoTrace<TE, E> extends IResult {

	public IProgramExecution<TE, E> getStem();

	public IProgramExecution<TE, E> getLasso();
}
