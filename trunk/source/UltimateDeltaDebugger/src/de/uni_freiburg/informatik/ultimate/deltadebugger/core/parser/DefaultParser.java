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

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ParserException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt.NoWorkspaceSavedFilesProvider;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.PSTBuilder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

public class DefaultParser implements Parser {
	static final int DEFAULT_OPTIONS = ILanguage.OPTION_NO_IMAGE_LOCATIONS | ILanguage.OPTION_IS_SOURCE_UNIT;

	static final String DEFAULT_FILEPATH = "<input>";

	final String dummySourceFilePath;
	final ScannerInfo scannerInfo;
	final IncludeFileContentProvider includeFileContentProvider;
	final IParserLogService parserLogService;

	public DefaultParser() {
		this(DEFAULT_FILEPATH);
	}

	public DefaultParser(final String dummySourceFilePath) {
		this(dummySourceFilePath, new ScannerInfo(), IncludeFileContentProvider.getEmptyFilesProvider(),
				new NullLogService());
	}

	public DefaultParser(final String dummySourceFilePath, final ScannerInfo scannerInfo,
			final IncludeFileContentProvider includeFileContentProvider, final IParserLogService parserLogService) {
		this.dummySourceFilePath = Objects.requireNonNull(dummySourceFilePath);
		this.scannerInfo = Objects.requireNonNull(scannerInfo);
		this.includeFileContentProvider = Objects.requireNonNull(includeFileContentProvider);
		this.parserLogService = Objects.requireNonNull(parserLogService);
	}

	public DefaultParser(final String dummySourceFilePath, final String[] includeFilePaths,
			final String[] localIncludePaths) {
		this(dummySourceFilePath, new ExtendedScannerInfo(null, includeFilePaths, null, null, localIncludePaths),
				new NoWorkspaceSavedFilesProvider(), new NullLogService());
	}

	@Override
	public IPSTTranslationUnit createPST(final IASTTranslationUnit ast, final ISourceDocument sourceDocument) {
		return new PSTBuilder(ast, sourceDocument).build();
	}

	@Override
	public IASTTranslationUnit parse(final String source) {
		return parse(source, DEFAULT_OPTIONS);
	}

	@Override
	public IASTTranslationUnit parse(final String source, final int options) {
		try {
			return GCCLanguage.getDefault().getASTTranslationUnit(
					FileContent.create(dummySourceFilePath, source.toCharArray()), scannerInfo,
					includeFileContentProvider, null, options, parserLogService);
		} catch (final CoreException e) {
			// No idea when and why this and why this would happen, so just wrap
			// the checked exception
			throw new ParserException(e);
		}
	}

}
