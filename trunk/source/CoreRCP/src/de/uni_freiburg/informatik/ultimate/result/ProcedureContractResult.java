package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Report a procedure contract that holds at ELEM which is a node in an 
 * Ultimate model.
 * The contract is given as an expression of type E.
 * @author Matthias Heizmann
 */
public class ProcedureContractResult<ELEM extends IElement, E> 
		extends AbstractResultAtElement<ELEM> implements IResultWithLocation {
	
	private E m_Contract;
	private final String m_ProcedureName;
	
	/**
	 * Constructor.
	 * @param location the Location
	 */
	public ProcedureContractResult(String plugin, ELEM position, 
			List<ITranslator<?,?,?,?>> translatorSequence,
			String procedureName, E contract) {
		super(position, plugin, translatorSequence);
		this.m_ProcedureName = procedureName;
		this.m_Contract = contract;
	}
	
	public E getContract() {
		return m_Contract;
	}

	@Override
	public String getShortDescription() {
		return "Procedure Contract for " + m_ProcedureName;
	}

	@Override
	public String getLongDescription() {
		StringBuffer sb = new StringBuffer();
		sb.append("Derived contract for procedure ");
		sb.append(m_ProcedureName);
		sb.append(": ");
		sb.append(ResultUtil.backtranslationWorkaround(
				m_TranslatorSequence, m_Contract));
		return sb.toString();
	}
}
