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
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Yannick Bühler
 * @since 2017-12-09
 */
public class FlatSymbolTable {
	/**
	 * Maps ACSL nodes to scopes
	 */
	private final Map<ACSLNode, Map<String, SymbolTableValue>> mACSLTable;
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
	 * Maps ACSL nodes to scope IDs
	 */
	private final Map<ACSLNode, Integer> mACSLScopeIDs;
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
	
	public FlatSymbolTable(final MultiparseSymbolTable mst, final Dispatcher disp) {
		mACSLTable = new LinkedHashMap<>();
		mCTable = new LinkedHashMap<>();
		mMultiparseInformation = mst; // TODO import into global scope!
		mScopeCounter = 1;
		mACSLScopeIDs = new HashMap<>();
		mCScopeIDs = new HashMap<>();
		mDispatcher = disp;
		mCHookSkip = n -> {
			if (n instanceof IASTExpression && n.getParent() instanceof IASTSwitchStatement) {
				if (((IASTSwitchStatement) n.getParent()).getControllerExpression() == n) {
					// the controller expression is not part of the scope of the switch (= its parent)
					// so the scope holder for the controller expression is the parent of the switch...
					return n.getParent().getParent();
				}
			}
			return n;
		};
		mBoogieIdToCId = new HashMap<>();
		mCDeclToBoogieDecl = new HashMap<>();
	}
	
	/**
	 * Implements the generic table lookup
	 * @param hook
	 * 			the hook which acts as an anchor for the current context in the AST
	 * @param id
	 * 			the id of the entry to look for
	 * @param table
	 * 			the table to check for entries
	 * @param parentProvider
	 * 			a function that maps a hook to its parent for traversal
	 * @param hookSkip
	 * 			as scopes might not only depend on the parentship relation (e.g. switch statement
	 * 			controller expressions) another layer of mapping is needed
	 * @param onlyInnermost
	 * 			if true, only the innermost scope will be searched
	 * @return the table entry or null
	 */
	private <T> SymbolTableValue genericTableFind(final T hook, final String id,
			final Map<T, Map<String, SymbolTableValue>> table, final Function<T, T> parentProvider,
			final Function<T, T> hookSkip, final boolean onlyInnermost) {
		T cursor = hookSkip.apply(hook);
		SymbolTableValue result = null;
		while (cursor != null) {
			if (table.containsKey(cursor)) {
				// This node has an associated scope, check whether the ID is found in that scope
				Map<String, SymbolTableValue> scope = table.get(cursor);
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
			cursor = parentProvider.apply(cursor);
			cursor = hookSkip.apply(cursor);
		}
		return result;
	}
	
	/**
	 * Lookup in the C-AST symbol table
	 * @see FlatSymbolTable#genericTableFind(Object, String, Map, Function)
	 */
	public SymbolTableValue findCSymbol(final IASTNode hook, final String id) {
		return genericTableFind(hook, id, mCTable, IASTNode::getParent, mCHookSkip, false);
	}
	
	/**
	 * Convenience method for checking if an entry exists
	 * @see FlatSymbolTable#findCSymbol(IASTNode, String)
	 */
	public boolean containsCSymbol(final IASTNode hook, final String id) {
		return findCSymbol(hook, id) != null;
	}
	
	/**
	 * Checks whether the entry with the given ID exists (or is shadowed) in the innermost scope
	 * @see FlatSymbolTable#containsCSymbol(IASTNode, String)
	 */
	public boolean containsCSymbolInInnermostScope(final IASTNode hook, final String id) {
		return genericTableFind(hook, id, mCTable, IASTNode::getParent, mCHookSkip, true) != null;
	}
	
	/**
	 * Fetches the unique scope ID at the given hook
	 * @param hook
	 * 			where in the AST to look for scopes
	 * @return the unique scope ID
	 */
	public int getCScopeId(final IASTNode hook) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			if (mCScopeIDs.containsKey(cursor)) {
				return mCScopeIDs.get(cursor);
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return 0;
	}
	
	/**
	 * Stores a value in the table
	 * @param hook
	 * 			anchor in the AST
	 * @param id
	 * 			the ID of the value
	 * @param val
	 * 			the value
	 * @param table
	 * 			the table to store values in
	 * @param parentProvider
	 * 			a function mapping a hook to its parent
	 * @param hookSkip
	 * 			as scopes might not only depend on the parentship relation (e.g. switch statement
	 * 			controller expressions) another layer of mapping is needed
	 * @param scopeHolderCheck
	 * 			a predicate matching all hooks that can hold scopes
	 * @param scopeInitializer
	 * 			called when a scope is initialized
	 * @see FlatSymbolTable#genericTableFind(Object, String, Map, Function, boolean)
	 */
	private <T> void genericTableStore(final T hook, final String id, final SymbolTableValue val,
			final Map<T, Map<String, SymbolTableValue>> table, final Function<T, T> parentProvider,
			final Function<T, T> hookSkip, final Predicate<T> scopeHolderCheck,
			final Consumer<T> scopeInitializer) {
		if (!mDispatcher.mTypeHandler.isStructDeclaration()) {
			T cursor = hookSkip.apply(hook);
			while (cursor != null) {
				if (scopeHolderCheck.test(cursor)) {
					// This node is the scope where values are currently stored inside
					table.computeIfAbsent(cursor, x -> {
						scopeInitializer.accept(x);
						return new LinkedHashMap<>();
					});
					table.get(cursor).put(id, val);
					break;
				}
				cursor = parentProvider.apply(cursor);
				cursor = hookSkip.apply(cursor);
			}
			if (cursor == null) {
				throw new IllegalStateException("Found no possible scope holder");				
			}
		}
	}
	
	/**
	 * Stores a C symbol
	 * @see FlatSymbolTable#genericTableStore(Object, String, SymbolTableValue, Map, Function, Function, Predicate)
	 */
	public void storeCSymbol(final IASTNode hook, final String id, final SymbolTableValue val) {
		genericTableStore(hook, id, val, mCTable, IASTNode::getParent, mCHookSkip, h -> {
			if (h instanceof IASTTranslationUnit) {
				// this node has the global scope
				return true;
			}
			if (h instanceof IASTFunctionDefinition || h instanceof IASTForStatement) {
				// this opens an implicit scope (for, functions)
				return true;
			}
			if (h instanceof IASTCompoundStatement) {
				// Watch out! Don't open a second scope for for-loops and functions
				return !(h.getParent() instanceof IASTForStatement)
						&& !(h.getParent() instanceof IASTFunctionDefinition);
			}
			return h instanceof IASTSwitchStatement;
		}, x -> mCScopeIDs.put(x, ++mScopeCounter));
		mBoogieIdToCId.put(val.getBoogieName(), id);
		mCDeclToBoogieDecl.put(val.getCDecl(), val.getBoogieDecl());
	}
	
	/**
	 * Fetches all values in the innermost C scope
	 * @param hook
	 * 			the anchor in the C AST
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
	 * @param filePath
	 *			The file the identifier is used in
	 * @param original
	 * 			The original identifier
	 * @return the new identifier (might be the same as before)
	 */
	public String applyMultiparseRenaming(final String filePath, final String original) {
		return mMultiparseInformation.getNameMappingIfExists(filePath, original);
	}
	
	/**
	 * Fetches the C ID for the given Boogie ID
	 * @param boogieId
	 * 			the boogie ID
	 * @return the C ID
	 */
	public String getCIdForBoogieId(final String boogieId) {
		return mBoogieIdToCId.get(boogieId);
	}
	
	/**
	 * Fetches the Boogie Declaration for the given C Declaration
	 * @param cDecl
	 * 			the C declaration
	 * @return the Boogie Declaration
	 */
	public Declaration getBoogieDeclForCDecl(final CDeclaration cDecl) {
		return mCDeclToBoogieDecl.get(cDecl);
	}
	
	/**
	 * Checks whether a variable with the given boogie ID is known, used for checking if
	 * a variable is a temporary variable
	 * @param boogieId
	 * 			the boogie ID
	 * @return whether the variable is contained in the symbol table
	 */
	public boolean containsBoogieSymbol(final String boogieId) {
		return mBoogieIdToCId.containsKey(boogieId);
	}
	
	/**
	 * Manually adds a C/Boogie ID pair to the symbol table
	 * @param boogieIdentifier
	 * 			the boogie ID
	 * @param cIdentifier
	 * 			the C ID
	 * @param loc
	 * 			the location, for error reporting
	 */
	public void addBoogieCIdPair(String boogieIdentifier, String cIdentifier, ILocation loc) {
		final String old = mBoogieIdToCId.put(boogieIdentifier, cIdentifier);
        if (old != null && !old.equals(cIdentifier)) {
            final String msg = "Variable with this name was already declared before:"
                    + cIdentifier;
            throw new IncorrectSyntaxException(loc, msg);
        }
	}
	
	/**
	 * Returns the Boogie to C ID mapping
	 * @return the boogie to C ID mapping
	 */
	public Map<String, String> getBoogieCIdentifierMapping() {
		return Collections.unmodifiableMap(mBoogieIdToCId);
	}
	
	/**
	 * Fetches the type of a variable
	 * @param hook
	 * 			where to look for the variable
	 * @param cId
	 * 			the c identifier
	 * @param loc 
	 * 			location for error reporting
	 * @return the type
	 */
	public ASTType getTypeOfVariable(IASTNode hook, String cId, ILocation loc) {
		return mDispatcher.mTypeHandler.cType2AstType(loc, findCSymbol(hook, cId).getCVariable());
	}
}
