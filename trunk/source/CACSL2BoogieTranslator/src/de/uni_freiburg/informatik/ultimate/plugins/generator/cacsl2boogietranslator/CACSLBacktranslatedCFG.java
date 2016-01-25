package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.core.services.BacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.model.structure.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.witnessprinter.CorrectnessWitnessGenerator;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CACSLBacktranslatedCFG extends BacktranslatedCFG<String, CACSLLocation>{

	private final Logger mLogger;

	public CACSLBacktranslatedCFG(final String filename, final IExplicitEdgesMultigraph<?, ?, String, CACSLLocation> cfg,
			final Class<CACSLLocation> clazz, final Logger logger) {
		super(filename, cfg, clazz);
		mLogger = logger;
	}
	
	@Override
	public String getSVCOMPWitnessString() {
		return new CorrectnessWitnessGenerator<CACSLLocation, IASTExpression>(this, new CACSLBacktranslationValueProvider(),
				mLogger).makeGraphMLString();
	}

}
