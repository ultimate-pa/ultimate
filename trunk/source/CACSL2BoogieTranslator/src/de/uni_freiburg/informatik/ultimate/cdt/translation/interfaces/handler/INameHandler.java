/*
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
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
 *
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.03.2012
 */
public interface INameHandler {
	/**
	 * Creates an unique (in translation unit) identifier for each variable.
	 *
	 * @param scope
	 *            should be IASTTranslationUnit, IASTCompoundStatement.
	 * @param cId
	 *            the name of the C variable.
	 * @param compCnt
	 *            the counter value of the compoundCntUID
	 * @param cType
	 *            CType of the object for which we need an identifier
	 * @return an unique identifier.
	 */
	public String getUniqueIdentifier(IASTNode scope, String cId, int compCnt, boolean isOnHeap, CType cType);

	/**
	 * Creates a unique identifier for temporary variables.
	 *
	 * @return a unique identifier for temporary variables.
	 */
	String getTempVarUID(AUXVAR purpose, CType cType);

	/**
	 * Create identifier for in-parameter of Boogie procedure.
	 *
	 * @param cid
	 *            the name of the C procedure parameter
	 * @param cType
	 *            CType of the object for which we need an identifier
	 * @return identifier for in-parameter of Boogie procedure.
	 */
	String getInParamIdentifier(String cid, CType cType);

	public String getGloballyUniqueIdentifier(String looplabel);

	public boolean isTempVar(String id);

	public String getTempVarUIDForBlockScope(AUXVAR auxVarType, CType cType);
}
