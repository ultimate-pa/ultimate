package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;

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
 */
public class CounterExampleResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM> implements
		IResultWithTrace {
	private final Check mCheckedSpecification;
	private String mProgramExecutionAsString;
	private final List<ILocation> mFailurePath;
	private final IProgramExecution<TE, E> mProgramExecution;

	public CounterExampleResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, E> pe) {
		super(position, plugin, translatorSequence);
		mCheckedSpecification = ResultUtil.getCheckedSpecification(position);
		mProgramExecution = pe;
		mFailurePath = getLocationSequence(pe);
	}

	@Override
	public String getShortDescription() {
		if (mCheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		} else {
			return mCheckedSpecification.getNegativeMessage();
		}
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("We found a FailurePath: ");
		sb.append(System.getProperty("line.separator"));
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
			mProgramExecutionAsString = m_TranslatorSequence.translateProgramExecution(mProgramExecution).toString();
		}
		return mProgramExecutionAsString;
	}

	private static <TE extends IElement, E> List<ILocation> getLocationSequence(IProgramExecution<TE, E> pe) {
		List<ILocation> result = new ArrayList<ILocation>();
		for (int i = 0; i < pe.getLength(); i++) {
			AtomicTraceElement<TE> te = pe.getTraceElement(i);
			result.add(te.getTraceElement().getPayload().getLocation());
		}
		return result;
	}

}
