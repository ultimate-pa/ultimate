/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General  License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General  License for more details.
 *
 * You should have received a copy of the GNU Lesser General  License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse  License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Describes a Type Handler.
 * It basically treats all sub-interfaces which derive from IASTDeclSpecifier.
 * We do not treat especially the main interface because only the sub-interfaces,
 * are interesting for us.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.02.2012
 */
public interface ITypeHandler extends IHandler {

	/**
	 * Translates an IASTSimpleDeclSpecifier. Basically treats all the build in types of C
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(IDispatcher main, IASTSimpleDeclSpecifier node);

	/**
	 * Translates an IASTNamedTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(IDispatcher main, IASTNamedTypeSpecifier node);

	/**
	 * Translates an IASTEnumerationSpecifier.
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(IDispatcher main, IASTEnumerationSpecifier node);

	/**
	 * Translates an IASTElaboratedTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(IDispatcher main, IASTElaboratedTypeSpecifier node);

	/**
	 * Translates an IASTCompositeTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(IDispatcher main, IASTCompositeTypeSpecifier node);

	/**
	 * Returns the type of the field in the struct.
	 *
	 * @param sT
	 *            the current symbolTable.
	 * @param loc
	 *            the location, where errors should be set, if there are any!
	 * @param lhs
	 *            the LHS.
	 * @return the type of the field <code>fieldId</code> in struct <code>structId</code>.
	 */
	ASTType getTypeOfStructLHS(final FlatSymbolTable sT, final ILocation loc, final StructLHS lhs, final IASTNode hook);

	/**
	 * Returns a list of undefined type identifiers.
	 *
	 * @return a list of undefined type identifiers
	 */
	Set<String> getUndefinedTypes();

	/**
	 * Compute the corresponding ASTType from a given CType.
	 *
	 * @param loc
	 * @param cType
	 * @return
	 */
	ASTType cType2AstType(ILocation loc, CType cType);

	/**
	 * Begin a scope for all Scoped Maps and Sets. (Types are scoped, too..)
	 */
	void beginScope();

	/**
	 * Begin a scope for all Scoped Maps and Sets. (Types are scoped, too..)
	 */
	void endScope();

	void addDefinedType(String id, TypesResult type);

	ASTType constructPointerType(ILocation loc);

	BoogieType getBoogiePointerType();

	BoogieType astTypeToBoogieType(ASTType astType);

	BoogieType getBoogieTypeForSizeT();

	BoogieType getBoogieTypeForBoogieASTType(ASTType valueAstType);

	BoogieType getBoogieTypeForPointerComponents();

	BoogieType getBoogieTypeForCType(CType resultType);

	ASTType byteSize2AstType(ILocation loc, CPrimitiveCategory inttype, int bytesize);

	boolean areFloatingTypesNeeded();

	void registerNamedIncompleteType(String incompleteType, String named);
}
