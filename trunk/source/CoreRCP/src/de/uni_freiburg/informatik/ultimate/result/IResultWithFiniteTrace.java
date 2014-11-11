package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * {@link IResultWithFiniteTrace} describes results that contain a finite trace.
 * The trace consists of trace elements of type TE. Furthermore, the trace is
 * described by (a) a sequence of {@link ILocation} and (b) by a
 * {@link IProgramExecution} that may contain program states, which are
 * described by expressions of type E.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
public interface IResultWithFiniteTrace<TE, E> extends IResult {

	public List<ILocation> getFailurePath();

	public IProgramExecution<TE, E> getProgramExecution();
}
