/*
 * Copyright (C) 2017 Yannick Bühler (buehlery@tf.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
 * Flat hierarchy rewrite of the old symbol table for the compiler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Yannick Bühler
 * @since 2017-12-09
 */
public class FlatSymbolTable {
	/**
	 * The global scope, spanning all translation units. Every translation unit points to this scope.
	 */
	private final Map<String, SymbolTableValue> mGlobalScope;
	/**
	 * Maps C nodes to scopes
	 */
	private final Map<IASTNode, Map<String, SymbolTableValue>> mCTable;
	/**
	 * The information that was collected about the multiparse project by the CDTParser
	 */
	private final MultiparseSymbolTable mMultiparseInformation;
	/**
	 * Used for assigning unique IDs to scopes
	 */
	private int mScopeCounter;
	/**
	 * Maps C nodes to scope IDs
	 */
	private final Map<IASTNode, Integer> mCScopeIDs;
	/**
	 * The dispatcher is needed to get necessary informations about the compilation
	 */
	private final Dispatcher mDispatcher;
	/**
	 * The non-trivial skip relation in the C-AST regarding scopes
	 */
	private final Function<IASTNode, IASTNode> mCHookSkip;
	/**
	 * Maps Boogie IDs to C IDs
	 */
	private final Map<String, String> mBoogieIdToCId;
	/**
	 * Maps C Declarations to Boogie Declarations
	 */
	private final Map<CDeclaration, Declaration> mCDeclToBoogieDecl;
	/**
	 * The name handler.
	 */
	private final INameHandler mNameHandler;
	
	public FlatSymbolTable(final MultiparseSymbolTable mst, final Dispatcher disp, final INameHandler nameHandler) {
		mGlobalScope = new LinkedHashMap<>();
		mCTable = new LinkedHashMap<>();
		mMultiparseInformation = mst;
		mScopeCounter = 1;
		mCScopeIDs = new HashMap<>();
		mDispatcher = disp;
		mCHookSkip = n -> {
			if (n instanceof IASTExpression && n.getParent() instanceof IASTSwitchStatement) {
				if (((IASTSwitchStatement) n.getParent()).getControllerExpression() == n) {
					// the controller expression is not part of the scope of the switch
					// so the scope holder for the controller expression is the parent of the switch...
					return n.getParent().getParent();
				}
			}
			return n;
		};
		mBoogieIdToCId = new HashMap<>();
		mCDeclToBoogieDecl = new HashMap<>();
		
		mNameHandler = nameHandler;
		// importAllGlobals(nameHandler);
	}
	
	/**
	 * Extracts all global variables into the global scope
	 */
	private void importAllGlobals(final INameHandler nameHandler) {
		Map<Pair<String, String>, IASTDeclarator> globals = mMultiparseInformation.getGlobalScope();
		for (Map.Entry<Pair<String, String>, IASTDeclarator> entry : globals.entrySet()) {
			final String uId = mMultiparseInformation.getNameMappingIfExists(entry.getKey().getFirst(), 
					entry.getKey().getSecond());
			
			// This entry is minimal, as some of the information is not available yet.
			// Need to somehow get a real SymbolTableValue here... at least the CDeclaration is required.
			final String bId = nameHandler.getUniqueIdentifier(null, uId, getCScopeId(entry.getValue()), false, null);
			final SymbolTableValue stv = new SymbolTableValue(bId, null, null, true, entry.getValue(), false);
			mGlobalScope.put(uId, stv);
		}
	}

	/**
	 * Implements the generic table lookup
	 * 
	 * @param hook
	 *            the hook which acts as an anchor for the current context in the AST
	 * @param id
	 *            the id of the entry to look for
	 * @param onlyInnermost
	 *            if true, only the innermost scope will be searched
	 * @return the table entry or null
	 */
	private SymbolTableValue tableFind(final IASTNode hook, final String id, final boolean onlyInnermost) {
		IASTNode cursor = mCHookSkip.apply(hook);
		SymbolTableValue result = null;
		while (cursor != null) {
			Map<String, SymbolTableValue> scope = null;
			if (cursor instanceof IASTTranslationUnit) {
				// This node references the global scope
				scope = mGlobalScope;
			} else if (mCTable.containsKey(cursor)) {
				// This node has an associated scope, check whether the ID is found in that scope
				scope = mCTable.get(cursor);
			}
			if (scope != null) {
				if (scope.containsKey(id)) {
					// This scope shadows all outer (=upper) scopes
					result = scope.get(id);
					break;
				}

				if (onlyInnermost) {
					// This node represents the innermost scope but doesn't contain the ID
					break;
				}
			}
			// Check the next level of the AST for scopes
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return result;
	}

	/**
	 * Lookup in the C-AST symbol table
	 * 
	 * @see FlatSymbolTable#tableFind(IASTNode, String, Map, boolean)
	 */
	public SymbolTableValue findCSymbol(final IASTNode hook, final String id) {
		return tableFind(hook, id, false);
	}

	/**
	 * Convenience method for checking if an entry exists
	 * 
	 * @see FlatSymbolTable#findCSymbol(IASTNode, String)
	 */
	public boolean containsCSymbol(final IASTNode hook, final String id) {
		return findCSymbol(hook, id) != null;
	}

	/**
	 * Checks whether the entry with the given ID exists (or is shadowed) in the innermost scope
	 * 
	 * @see FlatSymbolTable#containsCSymbol(IASTNode, String)
	 */
	public boolean containsCSymbolInInnermostScope(final IASTNode hook, final String id) {
		return tableFind(hook, id, true) != null;
	}

	/**
	 * Fetches the unique scope ID at the given hook
	 * 
	 * @param hook
	 *            where in the AST to look for scopes
	 * @return the unique scope ID
	 */
	public int getCScopeId(final IASTNode hook) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			if (cursor instanceof IASTTranslationUnit) {
				// The global scope is 1
				return 1;
			}
			final boolean hasImplicitScope =
					cursor instanceof IASTFunctionDefinition || cursor instanceof IASTForStatement;
			final boolean hasExplicitScope =
					cursor instanceof IASTCompoundStatement && !(cursor.getParent() instanceof IASTFunctionDefinition)
							&& !(cursor.getParent() instanceof IASTForStatement);
			if (hasImplicitScope || hasExplicitScope) {
				if (mCScopeIDs.containsKey(cursor)) {
					return mCScopeIDs.get(cursor);
				}
				mScopeCounter++;
				mCScopeIDs.put(cursor, mScopeCounter);
				return mScopeCounter;
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return 0;
	}

	/**
	 * Stores a value in the table
	 * 
	 * @param hook
	 *            anchor in the AST
	 * @param id
	 *            the ID of the value
	 * @param val
	 *            the value
	 * @see FlatSymbolTable#tableFind(IASTNode, String, boolean)
	 */
	private void tableStore(final IASTNode hook, final String id, final SymbolTableValue val) {
		if (mDispatcher.mTypeHandler == null || !mDispatcher.mTypeHandler.isStructDeclaration()) {
			IASTNode cursor = mCHookSkip.apply(hook);
			while (cursor != null) {
				if (cursor instanceof IASTTranslationUnit) {
					mGlobalScope.put(id, val);
					break;
				}
				final boolean hasImplicitScope =
						cursor instanceof IASTFunctionDefinition || cursor instanceof IASTForStatement;
				final boolean hasExplicitScope = cursor instanceof IASTCompoundStatement
						&& !(cursor.getParent() instanceof IASTFunctionDefinition)
						&& !(cursor.getParent() instanceof IASTForStatement);
				if (hasImplicitScope || hasExplicitScope) {
					// This node is the scope where values are currently stored inside
					mCTable.computeIfAbsent(cursor, x -> new LinkedHashMap<>());
					mCTable.get(cursor).put(id, val);
					break;
				}
				cursor = cursor.getParent();
				cursor = mCHookSkip.apply(cursor);
			}
			if (cursor == null) {
				throw new IllegalStateException("Found no possible scope holder");
			}
		}
	}

	/**
	 * Stores a C symbol
	 * 
	 * @see FlatSymbolTable#tableStore(IASTNode, String, SymbolTableValue)
	 */
	public void storeCSymbol(final IASTNode hook, final String id, final SymbolTableValue val) {
		tableStore(hook, id, val);
		mBoogieIdToCId.put(val.getBoogieName(), id);
		mCDeclToBoogieDecl.put(val.getCDecl(), val.getBoogieDecl());
	}

	/**
	 * Fetches all values in the innermost C scope
	 * 
	 * @param hook
	 *            the anchor in the C AST
	 * @return the values that are present in the innermost scope
	 */
	public Iterable<SymbolTableValue> getInnermostCScopeValues(final IASTNode hook) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			if (mCTable.containsKey(cursor)) {
				return Collections.unmodifiableCollection(mCTable.get(cursor).values());
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return Collections.emptyList();
	}

	/**
	 * Renames an identifier given the file it is in and the original name
	 * 
	 * @param filePath
	 *            The file the identifier is used in
	 * @param original
	 *            The original identifier
	 * @return the new identifier (might be the same as before)
	 */
	public String applyMultiparseRenaming(final String filePath, final String original) {
		return mMultiparseInformation.getNameMappingIfExists(filePath, original);
	}

	/**
	 * Fetches the C ID for the given Boogie ID
	 * 
	 * @param boogieId
	 *            the boogie ID
	 * @return the C ID
	 */
	public String getCIdForBoogieId(final String boogieId) {
		return mBoogieIdToCId.get(boogieId);
	}

	/**
	 * Fetches the Boogie Declaration for the given C Declaration
	 * 
	 * @param cDecl
	 *            the C declaration
	 * @return the Boogie Declaration
	 */
	public Declaration getBoogieDeclForCDecl(final CDeclaration cDecl) {
		return mCDeclToBoogieDecl.get(cDecl);
	}

	/**
	 * Checks whether a variable with the given boogie ID is known, used for checking if a variable is a temporary
	 * variable
	 * 
	 * @param boogieId
	 *            the boogie ID
	 * @return whether the variable is contained in the symbol table
	 */
	public boolean containsBoogieSymbol(final String boogieId) {
		return mBoogieIdToCId.containsKey(boogieId);
	}

	/**
	 * Manually adds a C/Boogie ID pair to the symbol table
	 * 
	 * @param boogieIdentifier
	 *            the boogie ID
	 * @param cIdentifier
	 *            the C ID
	 * @param loc
	 *            the location, for error reporting
	 */
	public void addBoogieCIdPair(final String boogieIdentifier, final String cIdentifier, final ILocation loc) {
		final String old = mBoogieIdToCId.put(boogieIdentifier, cIdentifier);
		if (old != null && !old.equals(cIdentifier)) {
			final String msg = "Variable with this name was already declared before:" + cIdentifier;
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	/**
	 * Returns the Boogie to C ID mapping
	 * 
	 * @return the boogie to C ID mapping
	 */
	public Map<String, String> getBoogieCIdentifierMapping() {
		return Collections.unmodifiableMap(mBoogieIdToCId);
	}

	/**
	 * Fetches the type of a variable
	 * 
	 * @param hook
	 *            where to look for the variable
	 * @param cId
	 *            the c identifier
	 * @param loc
	 *            location for error reporting
	 * @return the type
	 */
	public ASTType getTypeOfVariable(final IASTNode hook, final String cId, final ILocation loc) {
		return mDispatcher.mTypeHandler.cType2AstType(loc, findCSymbol(hook, cId).getCVariable());
	}
	
	/**
	 * Creates a boogie identifier.
	 * 
	 * @param scope
	 *            where the identifier is used
	 * @param scopeHook
	 *            where the identifier belongs to
	 * @param type
	 *            the type of the thing
	 * @param onHeap
	 *            whether the thing is on the heap
	 * @param cName
	 *            the original identifier in C
	 * @return the identifier
	 */
	public String createBoogieId(final IASTNode scope, final IASTNode scopeHook, final CType type, 
			final boolean onHeap, final String cName) {
		return mNameHandler.getUniqueIdentifier(scope, cName, getCScopeId(scopeHook), onHeap, type);
	}
}
