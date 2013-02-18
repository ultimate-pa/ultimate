package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;


/**
 * 
 * @author dietsch
 * @version 1.0.0
 */
public interface IOutput extends ITool  {
	/**
	 * Retrieve a list of traces to mark.
	 * 
	 * This method is called by the core whenever a modifying tool produced some
	 * traces which should be highlighted.
	 * @param traces List of all traces to highlight.
	 */
	public void setMarkedTraces(List<MarkedTrace> traces);

}
