/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.io.IOException;
import java.util.concurrent.TimeUnit;

import org.hamcrest.MatcherAssert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/***
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MonitoredProcessTest {

	private IUltimateServiceProvider mServices;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger(getClass());
	}

	@Test
	public void testProcessKill() throws IOException {
		final long timeoutInSeconds = 300;
		final MonitoredProcess mp;
		final long start = System.currentTimeMillis();
		mp = sleepExternal(timeoutInSeconds);
		MatcherAssert.assertThat("Did not create a process", mp != null);
		MatcherAssert.assertThat("Process is not running", mp.isRunning());
		final MonitoredProcessState mps = mp.impatientWaitUntilTime(1);
		final long stop = System.currentTimeMillis();
		MatcherAssert.assertThat("Process is not killed", mps.isKilled());
		MatcherAssert.assertThat("Process is still running", !mps.isRunning());
		final long killTime = stop - start;
		MatcherAssert.assertThat("Killing took more than 2s", killTime < 2000);
		mLogger.info("Took %s ms to kill", killTime);
	}

	@Test
	public void testProcessNormal() throws IOException {
		final long timeoutInSeconds = 1;
		final MonitoredProcess mp;
		final long start = System.currentTimeMillis();
		mp = sleepExternal(timeoutInSeconds);
		MatcherAssert.assertThat("Did not create a process", mp != null);
		MatcherAssert.assertThat("Process is not running", mp.isRunning());
		final MonitoredProcessState mps = mp.impatientWaitUntilTime(timeoutInSeconds * 2000);
		final long stop = System.currentTimeMillis();
		MatcherAssert.assertThat("Process is killed", !mps.isKilled());
		MatcherAssert.assertThat("Process is still running", !mps.isRunning());
		final long runtime = stop - start;
		MatcherAssert.assertThat("Runtime was longer than 3s", runtime < 3000);
		mLogger.info("Took %s ms to end", runtime);
	}

	@Test
	public void testProcessToolchainTimeout() throws IOException, InterruptedException {
		final long timeoutInSeconds = 300;
		final MonitoredProcess mp;
		final long start = System.currentTimeMillis();
		mServices.getProgressMonitorService().setDeadline(start + 1000);
		mp = sleepExternal(timeoutInSeconds);
		MatcherAssert.assertThat("Did not create a process", mp != null);
		MatcherAssert.assertThat("Process is not running", mp.isRunning());
		while (mServices.getProgressMonitorService().continueProcessing()) {
			TimeUnit.MILLISECONDS.sleep(50);
		}
		mp.waitfor(50);
		final long stop = System.currentTimeMillis();
		MatcherAssert.assertThat("Process is still running", !mp.isRunning());
		final long killTime = stop - start;
		MatcherAssert.assertThat("Killing took more than 2s", killTime < 2000);
		mLogger.info("Took %s ms to kill", killTime);
	}

	private MonitoredProcess sleepExternal(final long timeoutInSeconds) throws IOException {
		final MonitoredProcess mp;
		if (CoreUtil.OS_IS_WINDOWS) {
			mp = sleepWindows(timeoutInSeconds);
		} else {
			mp = sleepLinux(timeoutInSeconds);
		}
		return mp;
	}

	private MonitoredProcess sleepWindows(final long timeoutInS) throws IOException {
		return MonitoredProcess.exec(String.format("waitfor thiswillneverhappen /T %d", timeoutInS), null, mServices);
	}

	private MonitoredProcess sleepLinux(final long timeoutInS) throws IOException {
		return MonitoredProcess.exec(String.format("sleep %d", timeoutInS), null, mServices);
	}

}
