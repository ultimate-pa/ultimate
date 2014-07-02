/**
 * Main Handler for SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.SideEffectHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;

/**
 * TODO Currently only the old SV-COMP 2013 options are imitated.
 * 
 * @author Christian Schilling
 */
public class SvComp14MainDispatcher extends MainDispatcher {
	
    public SvComp14MainDispatcher(CACSL2BoogieBacktranslator backtranslator) {
		super(backtranslator);
	}
    
    @Override
    protected void init() {
        sideEffectHandler = new SideEffectHandler();
        cHandler = new SvComp14CHandler(this, backtranslator);
        typeHandler = new TypeHandler();
        acslHandler = new ACSLHandler();
        nameHandler = new NameHandler();
        preprocessorHandler = new SvComp14PreprocessorHandler();
        backtranslator.setBoogie2C(nameHandler.getBoogie2C());
        REPORT_WARNINGS = false;
    }
}
