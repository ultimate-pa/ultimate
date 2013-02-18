package local.stalin.SMTInterface.groundify;

import local.stalin.logic.Formula;
import local.stalin.logic.QuantifiedFormula;

public class QFRange {
	public QuantifiedFormula qf;
	public Formula skolemForm;
	// -1 means theory extension
	public int assnum;
	public QFRange(QuantifiedFormula qf,int assnum) {
		this.qf =  qf;
		skolemForm = qf;
		this.assnum = assnum;
	}
}
