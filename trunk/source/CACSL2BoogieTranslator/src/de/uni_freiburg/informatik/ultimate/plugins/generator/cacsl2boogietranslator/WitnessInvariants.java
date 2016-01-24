/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTNode;

/**
 * Wrapper object for information of correctness witness.
 * @author Matthias Heizmann
 *
 */
public class WitnessInvariants {

	private final Map<IASTNode, String> m_bInvariants;
	private final Map<IASTNode, String> m_aInvariants;

	public WitnessInvariants(Map<IASTNode, String> bInvariants, Map<IASTNode, String> aInvariants) {
		m_bInvariants = bInvariants;
		m_aInvariants = aInvariants;
	}

	public Map<IASTNode, String> getInvariantsBefore() {
		return m_bInvariants;
	}

	public Map<IASTNode, String> getInvariantsAfter() {
		return m_aInvariants;
	}
	
	

}
