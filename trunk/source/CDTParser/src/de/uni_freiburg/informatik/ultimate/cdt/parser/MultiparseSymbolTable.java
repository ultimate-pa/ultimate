/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTParser plug-in.
 *
 * The ULTIMATE CDTParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

import de.uni_freiburg.informatik.ultimate.cdt.parser.CDTParser;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.List;

/**
 * @author Yannick Bühler
 * @date 12.11.2017
 */
public class MultiparseSymbolTable extends ASTVisitor {
	/**
	 * The logger for printing stuff
	 */
	private final ILogger mLogger;
	/**
	 * A mapping (File Name, Identifier) -> Function definition
	 * (Not to a declaration, because only definitions have to be unique!)
	 */
	private final Map<Pair<String, String>, IASTFunctionDefinition> mFunctionMapping;
	/**
	 * A mapping (File Name, Identifier) -> Global variable declarator
	 */
	private final Map<Pair<String, String>, IASTDeclarator> mGlobalsMapping;
	/**
	 * A mapping (File Name, Identifier) -> Prefixed name that is unique
	 */
	private final Map<Pair<String, String>, String> mNamePrefixMapping;
	/**
	 * A mapping File Name -> List<File Name>
	 * which maps the files to the lists of files they include
	 */
	private final Map<String, List<String>> mIncludeMapping;
	
	/**
	 * Constructs an empty symbol table
	 * 
	 * @param logger a logger
	 */
	public MultiparseSymbolTable(final ILogger logger) {
		shouldVisitDeclarations = true;
		shouldVisitTranslationUnit = true;
		mLogger = logger;
		mFunctionMapping = new HashMap<>();
		mGlobalsMapping = new HashMap<>();
		mNamePrefixMapping = new HashMap<>();
		mIncludeMapping = new HashMap<>();
	}
	
	@Override
	public int visit(IASTTranslationUnit tu) {
		final String fileName = CDTParser.normalizeCDTFilename(tu.getFilePath());
		for (final IASTPreprocessorStatement stmt : tu.getAllPreprocessorStatements()) {
			if (stmt instanceof IASTPreprocessorIncludeStatement) {
				final IASTPreprocessorIncludeStatement include =
						(IASTPreprocessorIncludeStatement) stmt;
				
				if (include.isSystemInclude()) {
					// Ignore system includes for now
					mLogger.info("Ignoring system include " + include.getName());
					continue;
				}
				
				if (!include.isResolved()) {
					throw new UnsupportedOperationException("Includes need to be present in the multiparse project.");
				}
				final String includedFile = CDTParser.normalizeCDTFilename(include.getPath());
				
				mIncludeMapping.computeIfAbsent(fileName, x -> new ArrayList<>()).add(includedFile); 
			}
		}
		return super.visit(tu);
	}
	
	@Override
	public int visit(final IASTDeclaration declaration) {
		// Ignore non-top-level declarations
		if (!(declaration.getParent() instanceof IASTTranslationUnit)) {
			return super.visit(declaration);
		}

		final String fileNameRaw = ((IASTTranslationUnit) declaration.getParent()).getFilePath();
		final String fileName = CDTParser.normalizeCDTFilename(fileNameRaw);
		if (declaration instanceof IASTFunctionDefinition) {
			visitFunctionDefinition(fileName, (IASTFunctionDefinition) declaration);
		} else if (declaration instanceof IASTSimpleDeclaration) {
			for (final IASTDeclarator decl : ((IASTSimpleDeclaration) declaration).getDeclarators()) {
				if (!(decl instanceof IASTFunctionDeclarator)) {
					visitNonFunctionDeclarator(fileName, (IASTDeclarator) decl);
				}
			}
		}
		
		return super.visit(declaration);
	}
	
	private void visitNonFunctionDeclarator(final String inFile, final IASTDeclarator decl) {
		if (!decl.isPartOfTranslationUnitFile()) {
			// This indicates that the declaration comes from a resolved include
			// So this will not be put in the global variable table here
			return;
		}
		final Pair<String, String> entry = new Pair<>(inFile, decl.getName().toString());
		mGlobalsMapping.put(entry, decl);
		mNamePrefixMapping.put(entry, generatePrefixedIdentifier(inFile, decl.getName().toString()));
	}
	
	private void visitFunctionDefinition(final String inFile, final IASTFunctionDefinition fdef) {
		final IASTDeclarator fdecl = fdef.getDeclarator();
		final Pair<String, String> entry = new Pair<>(inFile, fdecl.getName().toString());
		mFunctionMapping.put(entry, fdef);
		mNamePrefixMapping.put(entry, generatePrefixedIdentifier(inFile, fdecl.getName().toString()));
	}
	
	private static String generatePrefixedIdentifier(final String file, final String id) {
		return "__U_MULTI_f" + file.replaceAll("[^a-zA-Z_]", "_") + "__" + id;
	}
	
	/**
	 * Prints the mappings for debug purposes
	 */
	public void printMappings() {
		mLogger.info("Include resolver:");
		for (Map.Entry<String, List<String>> entry : mIncludeMapping.entrySet()) {
			mLogger.info("File " + entry.getKey() + " includes: " + String.join(", ", entry.getValue()));
		}
		if (mIncludeMapping.isEmpty()) {
			mLogger.info("<empty include resolver>");
		}
		
		mLogger.info("Function table:");
		for (Pair<String, String> key : mFunctionMapping.keySet()) {
			final String newName = mNamePrefixMapping.get(key);
			mLogger.info("Function definition of " + newName + " in " + key.getFirst());
		}
		if (mFunctionMapping.isEmpty()) {
			mLogger.info("<empty function table>");
		}
		
		mLogger.info("Global variable table:");
		for (Pair<String, String> key : mGlobalsMapping.keySet()) {
			final String newName = mNamePrefixMapping.get(key);
			mLogger.info("Global variable declaration of " + newName + " in " + key.getFirst());
		}
		if (mGlobalsMapping.isEmpty()) {
			mLogger.info("<empty global variable table>");
		}
	}
	
	/**
	 * Applies a mapping of a unprefixed name to a prefixed name given the file the name was used in
	 * 
	 * @param filePath the file the name was used in. this is needed for include resolving / 'file-scopes'
	 * @param name the name that has to be mapped
	 * @return either the mapping of the name or the name itself if there is no such mapping
	 */
	public String getNameMappingIfExists(final String filePath, final String name) {
		final String normalizedFile = CDTParser.normalizeCDTFilename(filePath);
		final Pair<String, String> key = new Pair<>(normalizedFile, name);
		
		if (!mNamePrefixMapping.containsKey(key) && mIncludeMapping.containsKey(filePath)) {
			// This name might be defined in an included file
			// So we need to resolve the includes of the current file and check all included files too
			final List<String> includesOfFile = mIncludeMapping.get(filePath);
			for (final String include : includesOfFile) {
				// Just try keys until one fits. This works because the n included scopes may not clash
				final Pair<String, String> includeKey = new Pair<>(include, name);
				if (mNamePrefixMapping.containsKey(includeKey)) {
					return mNamePrefixMapping.get(includeKey);
				}
			}
		}
		
		// Fallback: Check the defined names in the file itself & if no definition is found, just use the original name,
		// i.e. no mapping of the name is performed.
		return mNamePrefixMapping.getOrDefault(key, name);
	}
}
