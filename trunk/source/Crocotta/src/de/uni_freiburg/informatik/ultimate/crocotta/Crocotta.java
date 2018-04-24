/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Crocotta plug-in.
 *
 * The ULTIMATE Crocotta plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Crocotta plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Crocotta plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Crocotta plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Crocotta plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.crocotta;

import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Concatenation;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.CrocottaAstVisitor;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Event;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.FinInfExpression;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.FixpointQuery;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.InclusionQuery;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Intersection;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.LanguageExpression;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Numeral;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Query;
import de.uni_freiburg.informatik.ultimate.crocotta.ast.Union;
import de.uni_freiburg.informatik.ultimate.crocotta.parser.CrocParser;

public class Crocotta implements ISource {
	private ILogger mLogger;
	private final List<String> mFileNames = new ArrayList<>();
	private IUltimateServiceProvider mServices;

	@Override
	public void init() {
		// not necessary
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
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	public boolean parseable(final File file) {
		return Arrays.stream(getFileTypes()).anyMatch(a -> file.getName().endsWith(a));
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files == null) {
			throw new AssertionError();
		}
		if (files.length != 1) {
			throw new UnsupportedOperationException(
					"Cannot parse more or less than one .croc file. You supplied " + files.length);
		}

		final FileReader reader = new FileReader(files[0]);
		final CrocParser parser = new CrocParser(mServices, mLogger, reader, files[0].getAbsolutePath());
		final Symbol goal = parser.parse();
		final Query[] queries = (Query[]) goal.value;

		for (final Query query : queries) {
			mLogger.info(new CrocottaQueryPrinter(query));
		}

		// process these queries or make a model out of them

		return null;
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".croc" };
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mFileNames);
		} catch (final Exception ex) {
			mLogger.fatal("syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		// not necessary
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// not necessary
	}

	private class CrocottaQueryPrinter extends CrocottaAstVisitor {

		private final StringBuilder mBuilder;

		public CrocottaQueryPrinter() {
			mBuilder = new StringBuilder();
		}

		public CrocottaQueryPrinter(final Query query) {
			this();
			query.accept(this);
		}

		@Override
		public boolean visit(final Concatenation node) {
			return printNAryOp("concat", node.getExpr());
		}

		private boolean printNAryOp(final String op, final LanguageExpression[] exprs) {
			mBuilder.append("(").append(op);
			Arrays.stream(exprs).forEach(a -> {
				mBuilder.append(" ");
				a.accept(this);
			});
			mBuilder.append(")");
			return false;
		}

		@Override
		public boolean visit(final Event node) {
			mBuilder.append("\"").append(node.getName()).append("\"");
			return false;
		}

		@Override
		public boolean visit(final FinInfExpression node) {
			mBuilder.append("(pair ");
			mBuilder.append(node.getFinite());
			mBuilder.append(", ");
			mBuilder.append(node.getInfinite());
			mBuilder.append(")");
			return false;
		}

		@Override
		public boolean visit(final FixpointQuery node) {
			mBuilder.append("[");
			node.getFinInfExpr().accept(this);
			mBuilder.append(" = ");
			node.getExpr().accept(this);
			mBuilder.append("]");
			return false;
		}

		@Override
		public boolean visit(final Intersection node) {
			return printNAryOp("intersect", node.getExpr());
		}

		@Override
		public boolean visit(final Union node) {
			return printNAryOp("union", node.getExpr());
		}

		@Override
		public boolean visit(final Numeral node) {
			mBuilder.append(node.getValue());
			return false;
		}

		@Override
		public boolean visit(final InclusionQuery node) {
			mBuilder.append("[");
			node.getLeft().accept(this);
			mBuilder.append(" <= ");
			node.getRight().accept(this);
			mBuilder.append("]");
			return super.visit(node);
		}

		@Override
		public String toString() {
			return mBuilder.toString();
		}
	}
}
