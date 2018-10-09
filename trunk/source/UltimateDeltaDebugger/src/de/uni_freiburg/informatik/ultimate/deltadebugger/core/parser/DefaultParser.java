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

import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage;
import org.eclipse.cdt.core.model.ILanguage;
import org.eclipse.cdt.core.parser.ExtendedScannerInfo;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.NullLogService;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.core.runtime.CoreException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ParserException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt.NoWorkspaceSavedFilesProvider;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.PSTBuilder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Default parser implementation.
 */
public class DefaultParser implements IParser {
	protected static final int DEFAULT_OPTIONS = ILanguage.OPTION_NO_IMAGE_LOCATIONS | ILanguage.OPTION_IS_SOURCE_UNIT;

	protected static final String DEFAULT_FILEPATH = "<input>";

	protected final ILogger mLogger;
	protected final String mDummySourceFilePath;
	protected final ScannerInfo mScannerInfo;
	protected final IncludeFileContentProvider mIncludeFileContentProvider;
	protected final IParserLogService mParserLogService;

	/**
	 * Default constructor.
	 *
	 * @param logger
	 *            logger instance
	 */
	public DefaultParser(final ILogger logger) {
		this(logger, DEFAULT_FILEPATH);
	}

	/**
	 * @param logger
	 *            logger instance
	 * @param dummySourceFilePath
	 *            Dummy source file path.
	 */
	public DefaultParser(final ILogger logger, final String dummySourceFilePath) {
		this(logger, dummySourceFilePath, new ScannerInfo(), IncludeFileContentProvider.getEmptyFilesProvider(),
				new NullLogService());
	}

	/**
	 * @param logger
	 *            logger instance
	 * @param dummySourceFilePath
	 *            Dummy source file path.
	 * @param scannerInfo
	 *            scanner info
	 * @param includeFileContentProvider
	 *            include file content provider
	 * @param parserLogService
	 *            parser log service
	 */
	public DefaultParser(final ILogger logger, final String dummySourceFilePath, final ScannerInfo scannerInfo,
			final IncludeFileContentProvider includeFileContentProvider, final IParserLogService parserLogService) {
		mLogger = Objects.requireNonNull(logger);
		mDummySourceFilePath = Objects.requireNonNull(dummySourceFilePath);
		mScannerInfo = Objects.requireNonNull(scannerInfo);
		mIncludeFileContentProvider = Objects.requireNonNull(includeFileContentProvider);
		mParserLogService = Objects.requireNonNull(parserLogService);
	}

	/**
	 * @param logger
	 *            logger instance
	 * @param dummySourceFilePath
	 *            Dummy source file path.
	 * @param includeFilePaths
	 *            include file paths
	 * @param localIncludePaths
	 *            local include paths
	 */
	public DefaultParser(final ILogger logger, final String dummySourceFilePath, final String[] includeFilePaths,
			final String[] localIncludePaths) {
		this(logger, dummySourceFilePath,
				new ExtendedScannerInfo(null, includeFilePaths, null, null, localIncludePaths),
				new NoWorkspaceSavedFilesProvider(), new NullLogService());
	}

	@Override
	public IPSTTranslationUnit createPst(final IASTTranslationUnit ast, final ISourceDocument sourceDocument) {
		return new PSTBuilder(mLogger, ast, sourceDocument).build();
	}

	@Override
	public IASTTranslationUnit parse(final String source) {
		return parse(source, DEFAULT_OPTIONS);
	}

	@Override
	public IASTTranslationUnit parse(final String source, final int options) {
		try {
			return GCCLanguage.getDefault().getASTTranslationUnit(
					FileContent.create(mDummySourceFilePath, source.toCharArray()), mScannerInfo,
					mIncludeFileContentProvider, null, options, mParserLogService);
		} catch (final CoreException e) {
			// No idea when and why this and why this would happen, so just wrap
			// the checked exception
			throw new ParserException(e);
		}
	}
}
