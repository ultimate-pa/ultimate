/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Main Handler for SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.SideEffectHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompTypeHandler;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BeforeAfterWitnessInvariantsMapping;

/**
 * TODO: rename this to 2015 perhaps??
 * @author Christian Schilling
 * @author nutz
 */
public class SvComp14MainDispatcher extends MainDispatcher {

	public SvComp14MainDispatcher(CACSL2BoogieBacktranslator backtranslator, BeforeAfterWitnessInvariantsMapping witnessInvariants, IUltimateServiceProvider services,
			Logger logger) {
		super(backtranslator, witnessInvariants, services, logger);
	}

	@Override
	protected void init() {
		sideEffectHandler = new SideEffectHandler();
		typeHandler = new SVCompTypeHandler(!m_BitvectorTranslation);
		acslHandler = new ACSLHandler(m_WitnessInvariants != null);
		nameHandler = new NameHandler(backtranslator);
		cHandler = new SvComp14CHandler(this, backtranslator, mLogger, typeHandler, m_BitvectorTranslation, m_OverapproximateFloatingPointOperations, nameHandler);
		this.backtranslator.setExpressionTranslation(((SvComp14CHandler) cHandler).getExpressionTranslation());
		preprocessorHandler = new SvComp14PreprocessorHandler();
		REPORT_WARNINGS = false;
	}
}
