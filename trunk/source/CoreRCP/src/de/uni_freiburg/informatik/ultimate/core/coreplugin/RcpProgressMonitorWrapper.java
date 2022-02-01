/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import org.eclipse.core.runtime.IProgressMonitor;

import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RcpProgressMonitorWrapper {

	public static IProgressMonitor create(IToolchainProgressMonitor tpm) {
		if (tpm instanceof Ultimate2RcpProgressMonitor) {
			return (IProgressMonitor) tpm;
		} else if (tpm instanceof Rcp2UltimateProgressMonitor) {
			return ((Rcp2UltimateProgressMonitor) tpm).mBacking;
		} else {
			return new Ultimate2RcpProgressMonitor(tpm);
		}
	}

	public static IToolchainProgressMonitor create(IProgressMonitor pm) {
		if (pm instanceof Ultimate2RcpProgressMonitor) {
			return ((Ultimate2RcpProgressMonitor) pm).mBacking;
		} else if (pm instanceof Rcp2UltimateProgressMonitor) {
			return (IToolchainProgressMonitor) pm;
		} else {
			return new Rcp2UltimateProgressMonitor(pm);
		}
	}

	private static final class Ultimate2RcpProgressMonitor implements IToolchainProgressMonitor, IProgressMonitor {

		private final IToolchainProgressMonitor mBacking;

		private Ultimate2RcpProgressMonitor(final IToolchainProgressMonitor backing) {
			mBacking = backing;
		}

		@Override
		public void beginTask(String name, int totalWork) {
			mBacking.beginTask(name, totalWork);
		}

		@Override
		public void done() {
			mBacking.done();
		}

		@Override
		public void internalWorked(double work) {
			mBacking.internalWorked(work);
		}

		@Override
		public boolean isCanceled() {
			return mBacking.isCanceled();
		}

		@Override
		public void setCanceled(boolean value) {
			mBacking.setCanceled(value);
		}

		@Override
		public void setTaskName(String name) {
			mBacking.setTaskName(name);
		}

		@Override
		public void subTask(String name) {
			mBacking.subTask(name);
		}

		@Override
		public void worked(int work) {
			mBacking.worked(work);
		}
	}

	private static final class Rcp2UltimateProgressMonitor implements IToolchainProgressMonitor, IProgressMonitor {

		private final IProgressMonitor mBacking;

		private Rcp2UltimateProgressMonitor(final IProgressMonitor backing) {
			mBacking = backing;
		}

		@Override
		public void beginTask(String name, int totalWork) {
			mBacking.beginTask(name, totalWork);
		}

		@Override
		public void done() {
			mBacking.done();
		}

		@Override
		public void internalWorked(double work) {
			mBacking.internalWorked(work);
		}

		@Override
		public boolean isCanceled() {
			return mBacking.isCanceled();
		}

		@Override
		public void setCanceled(boolean value) {
			mBacking.setCanceled(value);
		}

		@Override
		public void setTaskName(String name) {
			mBacking.setTaskName(name);
		}

		@Override
		public void subTask(String name) {
			mBacking.subTask(name);
		}

		@Override
		public void worked(int work) {
			mBacking.worked(work);
		}
	}
}
