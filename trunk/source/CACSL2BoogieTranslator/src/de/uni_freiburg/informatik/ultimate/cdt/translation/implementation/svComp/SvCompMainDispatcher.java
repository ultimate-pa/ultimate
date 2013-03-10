/**
 * Main Handler for SV-Comp.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.SideEffectHandler;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;

/**
 * @author Markus Lindenmann
 * @date 11.6.2012
 * 
 */
public class SvCompMainDispatcher extends MainDispatcher {
	
    public SvCompMainDispatcher(Backtranslator backtranslator) {
		super(backtranslator);
	}
    
    @Override
    protected void init() {
        sideEffectHandler = new SideEffectHandler();
        cHandler = new SvCompCHandler(this, backtranslator);
        typeHandler = new SVCompTypeHandler();
        acslHandler = new ACSLHandler();
        nameHandler = new NameHandler();
        preprocessorHandler = new PreprocessorHandler();
        backtranslator.setBoogie2C(nameHandler.getBoogie2C());
        REPORT_WARNINGS = false;
    }
}
