package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result to store that the specification given at some location does not always
 * holds. We also store a computerexample to the correctness of the
 * specification. This counterexample is given as list of locations. (Locations
 * of Statements which lead to a state that violates the specification.
 * 
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.01.2012
 * 
 * @param <ELEM>
 *            Type of position
 * @param <TE>
 *            Type of trace element
 * @param <E>
 *            Type of expression
 */
public class CounterExampleResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithFiniteTrace<TE, E> {
	private final Check mCheckedSpecification;
	private String mProgramExecutionAsString;
	private final List<ILocation> mFailurePath;
	private final IProgramExecution<TE, E> mProgramExecution;

	public CounterExampleResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, E> pe) {
		super(position, plugin, translatorSequence);
		mCheckedSpecification = ResultUtil.getCheckedSpecification(position);
		mProgramExecution = pe;
		mFailurePath = ResultUtil.getLocationSequence(pe);
	}

	@Override
	public String getShortDescription() {
		if (mCheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		} else {
			return mCheckedSpecification.getNegativeMessage();
		}
	}

	public Check getCheckedSpecification() {
		return mCheckedSpecification;
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("We found a FailurePath: ");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(getProgramExecutionAsString());
		return sb.toString();
	}

	/**
	 * Getter for the failure path.
	 * 
	 * @return the failurePath
	 */
	public List<ILocation> getFailurePath() {
		return mFailurePath;
	}

	public IProgramExecution<TE, E> getProgramExecution() {
		return mProgramExecution;
	}

	public String getProgramExecutionAsString() {
		if (mProgramExecutionAsString == null) {
			mProgramExecutionAsString = mTranslatorSequence.translateProgramExecution(mProgramExecution).toString();
		}
		return mProgramExecutionAsString;
	}
}
