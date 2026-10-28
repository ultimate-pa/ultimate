package de.uni_freiburg.informatik.ultimate.eca.parser;

import java.io.File;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.cup.generated.EcaParser;

public class EcaSource implements ISource {
	private final List<String> mFileNames = new ArrayList<>();
	private ILogger mLogger;
	private IUltimateServiceProvider mServices;

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getPluginID());
	}

	@Override
	public void init() {
		mFileNames.clear();
	}

	@Override
	public void finish() {
		// No resources are retained between calls.
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public File[] parseable(final File[] files) {
		return Arrays.stream(files).filter(file -> file.isFile() && file.getName().endsWith(".eca"))
				.toArray(File[]::new);
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files == null || files.length != 1 || !files[0].isFile() || !files[0].getName().endsWith(".eca")) {
			throw new IllegalArgumentException("Expected exactly one .eca file");
		}
		final File file = files[0];
		final String fileName = file.getAbsolutePath();
		if (mLogger != null) {
			mLogger.info("Parsing " + fileName);
		}
		final EcaFile ast;
		try (Reader reader = Files.newBufferedReader(file.toPath(), StandardCharsets.UTF_8)) {
			ast = new EcaParser(reader, fileName).parseFile();
		}
		final List<EcaTypeChecker.Diagnostic> diagnostics = new EcaTypeChecker().check(ast);
		if (!diagnostics.isEmpty()) {
			for (final EcaTypeChecker.Diagnostic diagnostic : diagnostics) {
				if (mLogger != null) {
					mLogger.error(diagnostic.toString());
				}
				if (mServices != null) {
					final ObjectContainer<EcaFile> errorElement = new ObjectContainer<>(ast);
					if (diagnostic.location() != null) {
						diagnostic.location().annotate(errorElement);
					}
					mServices.getResultService().reportResult(getPluginID(), new TypeErrorResult<>(errorElement,
							getPluginID(), mServices.getBacktranslationService(), diagnostic.message()));
				}
			}

			if (mServices != null) {
				mServices.getProgressMonitorService().cancelToolchain();
			}
			throw new IllegalArgumentException("ECA type checking failed: " + diagnostics.get(0));
		}
		mFileNames.add(fileName);
		return new ObjectContainer<>(ast);
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".eca" };
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(getPluginID(), ModelType.Type.OTHER, mFileNames);
	}

}
