/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ScannerInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.PSTACSLBuilder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.PSTBuilder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.ACSLNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Default parser implementation with parsed ACSL nodes in the PST
 */
public class DefaultParserWithACSL extends DefaultParser {

	public DefaultParserWithACSL(ILogger logger, String dummySourceFilePath, ScannerInfo scannerInfo,
			IncludeFileContentProvider includeFileContentProvider, IParserLogService parserLogService) {
		super(logger, dummySourceFilePath, scannerInfo, includeFileContentProvider, parserLogService);
	}

	public DefaultParserWithACSL(ILogger logger, String dummySourceFilePath, String[] includeFilePaths,
			String[] localIncludePaths) {
		super(logger, dummySourceFilePath, includeFilePaths, localIncludePaths);
	}

	public DefaultParserWithACSL(ILogger logger, String dummySourceFilePath) {
		super(logger, dummySourceFilePath);
	}

	public DefaultParserWithACSL(ILogger logger) {
		super(logger);
	}

	@Override
	public IPSTTranslationUnit createPst(IASTTranslationUnit ast, ISourceDocument sourceDocument) {
		final IPSTTranslationUnit pst = new PSTBuilder(mLogger, ast, sourceDocument)
				.setNodeFactory(new ACSLNodeFactory()).build();
		PSTACSLBuilder.build(pst, mLogger);
		return pst;
	}
}
