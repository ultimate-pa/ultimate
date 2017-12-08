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
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.02.2012
 */
public interface ITypeHandler extends IHandler {

	/**
	 * Whether the current declaration is a struct declaration.
	 *
	 * @return true, iff struct field declarations are dispatched.
	 */
	boolean isStructDeclaration();

	/**
	 * Translates an IASTSimpleDeclSpecifier. Basically treats all the build in types of C
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(Dispatcher main, IASTSimpleDeclSpecifier node);

	/**
	 * Translates an IASTNamedTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(Dispatcher main, IASTNamedTypeSpecifier node);

	/**
	 * Translates an IASTEnumerationSpecifier.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(Dispatcher main, IASTEnumerationSpecifier node);

	/**
	 * Translates an IASTElaboratedTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node);

	/**
	 * Translates an IASTCompositeTypeSpecifier.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	Result visit(Dispatcher main, IASTCompositeTypeSpecifier node);

	/**
	 * Translates an CDT IType to a Boogie type.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param type
	 *            the node to visit
	 * @return a result object
	 */
	InferredType visit(Dispatcher main, IType type);

	/**
	 * Translates an CDT IBasicType to a Boogie type. This includes ICBasicType and CBasicType.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param type
	 *            the node to visit
	 * @return a result object
	 */
	InferredType visit(final Dispatcher main, final IBasicType type);

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
	ASTType getTypeOfStructLHS(final SymbolTable sT, final ILocation loc, final StructLHS lhs);

	/**
	 * Translates an CDT ITypedef to a Boogie type.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param type
	 *            the node to visit
	 * @return a result object
	 */
	InferredType visit(Dispatcher main, ITypedef type);

	/**
	 * Translates an CDT IArrayType to a Boogie type.
	 *
	 * @param main
	 *            a reference to the main dispatcher
	 * @param type
	 *            the node to visit
	 * @return a result objectd
	 */
	InferredType visit(Dispatcher main, IArrayType type);

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

	/**
	 * Return the map of type aliases coming from C-typedefs.
	 */
	LinkedScopedHashMap<String, TypesResult> getDefinedTypes();

	void addDefinedType(String id, TypesResult type);

	ASTType constructPointerType(ILocation loc);

	ICHandler getCHandler();

	void setCHandler(CHandler cHandler);
}
