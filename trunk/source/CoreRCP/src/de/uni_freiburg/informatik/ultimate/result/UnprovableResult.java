package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * Result to store that we are not able to determine if a specification given at
 * some location holds. We also provide a potential counterexample for which one
 * of the following holds.
 * <ul>
 * <li>We are not able to determine feasibility of the counterexample. (e.g.,
 * multiplication of variables and LIRA logic, timeout of solver,..)
 * <li>We are not able to exclude the counterexample in the refined abstraction.
 * (e.g., predicate abstraction with fixed set of predicates)
 * </ul>
 * If the fail of a model checker is not related to one specific counterexample
 * we use the timeout result.
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
public class UnprovableResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithFiniteTrace<TE, E> {

	private final Check mCheckedSpecification;
	private final IProgramExecution<TE, E> mProgramExecution;
	private final List<ILocation> mFailurePath;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the Location
	 */
	public UnprovableResult(String plugin, ELEM position, IBacktranslationService translatorSequence,
			IProgramExecution<TE, E> programExecution) {
		super(position, plugin, translatorSequence);
		Check check = ResultUtil.getCheckedSpecification(position);
		if (check == null) {
			mCheckedSpecification = new Check(Spec.UNKNOWN);
		} else {
			mCheckedSpecification = check;
		}
		mProgramExecution = programExecution;
		mFailurePath = ResultUtil.getLocationSequence(programExecution);
	}

	@Override
	public String getShortDescription() {
		return "Unable to prove that " + mCheckedSpecification.getPositiveMessage();
	}

	@Override
	public String getLongDescription() {
		return "Unable to prove that " + mCheckedSpecification.getPositiveMessage();
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
}
