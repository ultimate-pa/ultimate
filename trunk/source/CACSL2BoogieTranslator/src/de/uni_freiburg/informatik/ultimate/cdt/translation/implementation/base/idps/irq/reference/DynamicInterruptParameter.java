/*
 * Copyright (C) 2026 Manuel Bentele
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE
 * CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE CACSL2BoogieTranslator plug-in,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing
 * parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE CACSL2BoogieTranslator
 * plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.reference;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequest;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequestHandler;

/**
 * Interrupt request (IRQ) reference for one specific runtime interrupt supplied as a procedure parameter.
 *
 * @author Manuel Bentele
 */
public final class DynamicInterruptParameter extends SingleInterrupt<VarList> {

	public DynamicInterruptParameter(final VarList ref) {
		super(ref);
	}

	@Override
	public List<InterruptRequest> resolve(final InterruptRequestHandler handler) {
		// TODO
	}

}