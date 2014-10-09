/**
 * Main Handler for SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.SideEffectHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompTypeHandler;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;

/**
 * TODO: rename this to 2015 perhaps??
 * @author Christian Schilling
 * @author nutz
 */
public class SvComp14MainDispatcher extends MainDispatcher {

	public SvComp14MainDispatcher(CACSL2BoogieBacktranslator backtranslator, IUltimateServiceProvider services,
			Logger logger) {
		super(backtranslator, services, logger);
	}

	@Override
	protected void init() {
		sideEffectHandler = new SideEffectHandler();
		typeHandler = new SVCompTypeHandler();
		acslHandler = new ACSLHandler();
		nameHandler = new NameHandler();
		cHandler = new SvComp14CHandler(this, backtranslator, mLogger, typeHandler);
		preprocessorHandler = new SvComp14PreprocessorHandler();
		backtranslator.setBoogie2C(nameHandler.getBoogie2C());
		REPORT_WARNINGS = false;
	}
}
