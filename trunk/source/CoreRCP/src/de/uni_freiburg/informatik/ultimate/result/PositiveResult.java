package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Result to store that the specification given at some location always holds. 
 * The specification at this location may explicitly (e.g., there is a assert
 * statement at this location) or implicitly (e.g. at this location a pointer is
 * dereferenced and the programming language does not allow dereference of 
 * nullpointers).
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 27.03.2012
 */
public class PositiveResult<ELEM extends IElement> extends AbstractResultAtElement<ELEM> implements IResult {
	private final Check m_CheckedSpecification;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 */
	public PositiveResult(String plugin, ELEM position, 
			IBacktranslationService translatorSequence) {
		super(position, plugin, translatorSequence);
		m_CheckedSpecification = ResultUtil.getCheckedSpecification(position);
	}

	@Override
	public String getShortDescription() {
		if (m_CheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		} else {
			return m_CheckedSpecification.getPositiveMessage();
		}
	}

	@Override
	public String getLongDescription() {
		if (m_CheckedSpecification == null) {
			return "some specification holds - ERROR (information lost during translation process)";
		} else {
			StringBuilder sb = new StringBuilder();
			sb.append("For all program executions holds that ");
			sb.append(m_CheckedSpecification.getPositiveMessage());
			sb.append(" at this location");
			return sb.toString();
		}

	}

}
