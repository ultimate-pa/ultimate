/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue.Bool;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue;

/**
 * @author Christopher Dillo
 *
 */
public class BoolMergeWideningOperator implements IMergeOperator,
		IWideningOperator {

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return BoolDomainFactory.s_DomainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#getName()
	 */
	@Override
	public String getName() {
		return "BOOL Merge & Widening";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public BoolValue apply(IAbstractValue valueA, IAbstractValue valueB) {
		BoolValue bvalA = (BoolValue) valueA;
		BoolValue bvalB = (BoolValue) valueB; 
		
		// invalid state objects
		if ((bvalA == null) || (bvalB == null)) {
			return null;
		}
		
		Bool boolA = bvalA.getValue();
		Bool boolB = bvalB.getValue();
		
		if (boolA == boolB) return new BoolValue(boolA);

		if (boolA == Bool.EMPTY) {
			if (boolB == Bool.TRUE) return new BoolValue(Bool.TRUE);
			if (boolB == Bool.FALSE) return new BoolValue(Bool.FALSE);
		}
		if (boolB == Bool.EMPTY) {
			if (boolA == Bool.TRUE) return new BoolValue(Bool.TRUE);
			if (boolA == Bool.FALSE) return new BoolValue(Bool.FALSE);
		}
		
		return new BoolValue(Bool.UNKNOWN);
	}

}
