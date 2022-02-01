/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan.extension;

import org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker;
import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICElement;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;

/**
 * So we need this Extension, because Codan uses internally the
 * 
 * PARSE_OPTION =
 * ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS
 * 
 * So we have no trivial values in Arrays Initializer, this class solves this
 * problem. In order to do this we did not use any longer the internal Codan
 * Model Cache.
 * 
 * @author Stefan Wissert
 * 
 */
public abstract class AbstractFullAstChecker extends AbstractIndexAstChecker {

	/**
	 * Parsing Options for creating the used AST
	 */
	private static final int PARSE_MODE = ITranslationUnit.AST_SKIP_ALL_HEADERS
			| ITranslationUnit.AST_CONFIGURE_USING_SOURCE_CONTEXT
			| ITranslationUnit.AST_PARSE_INACTIVE_CODE;

	private IFile file;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker#getFile()
	 */
	@Override
	protected IFile getFile() {
		return file;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.cdt.codan.core.cxx.model.AbstractIndexAstChecker#processResource
	 * (org.eclipse.core.resources.IResource)
	 */
	@Override
	public synchronized boolean processResource(IResource resource)
			throws OperationCanceledException {
		if (!shouldProduceProblems(resource)) {
			return false;
		}
		if (!(resource instanceof IFile)) {
			return true;
		}

		processFile((IFile) resource);
		return false;
	}

	/**
	 * This methods generate a AST out of a File
	 * 
	 * @param file
	 * @throws OperationCanceledException
	 */
	private void processFile(IFile file) throws OperationCanceledException {
		this.file = file;
		final ICElement celement = CoreModel.getDefault().create(file);
		if (!(celement instanceof ITranslationUnit)) {
			return;
		}
		final ITranslationUnit tu = (ITranslationUnit) celement;
		ICProject[] projects;
		try {
			projects = CoreModel.getDefault().getCModel().getCProjects();
			final IIndex index = CCorePlugin.getIndexManager().getIndex(projects);
			index.acquireReadLock();
			final IASTTranslationUnit ast = tu.getAST(index, PARSE_MODE);
			if (ast != null) {
				synchronized (ast) {
					processAst(ast);
				}
			}
		} catch (final CModelException e1) {
			e1.printStackTrace();
		} catch (final CoreException e) {
			e.printStackTrace();
		} catch (final InterruptedException e) {
			e.printStackTrace();
		}
	}
}
