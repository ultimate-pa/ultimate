package de.uni_freiburg.informatik.ultimate.cloud;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.security.InvalidKeyException;

import com.microsoft.windowsazure.services.blob.client.CloudBlob;
import com.microsoft.windowsazure.services.blob.client.CloudBlobClient;
import com.microsoft.windowsazure.services.blob.client.CloudBlobContainer;
import com.microsoft.windowsazure.services.core.storage.CloudStorageAccount;
import com.microsoft.windowsazure.services.core.storage.StorageException;
import com.microsoft.windowsazure.services.queue.client.CloudQueue;
import com.microsoft.windowsazure.services.queue.client.CloudQueueClient;
import com.microsoft.windowsazure.services.queue.client.CloudQueueMessage;

import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;

public class UltimateCloud implements IUltimate {

	private CloudStorageAccount account;

	private String credentials = "DefaultEndpointsProtocol=http;"
			+ "AccountName=stalin;"
			+ "AccountKey=BTfAG0/OAC1tKT0olcHmpqjSfYUaMYiB8bNpZPWN25B/jpM1lMO/7OQKomGmtzx+ZYYQ3bVlKrZQmeH4BgJ9Kg==";

	public UltimateCloud() {

		try {
			account = CloudStorageAccount.parse(credentials);
		} catch (InvalidKeyException e) {
			e.printStackTrace();
		} catch (URISyntaxException e) {
			e.printStackTrace();
		}

	}

	public IResult getResult(String id) {
		return null;
	}

	public void startUltimate(String taskName, String settingsFile,
			Toolchain toolchain, String code) {

		CloudBlobContainer blobContainer = initBlob(taskName);

		// Upload toolchain to blob storage
		String toolchainXML = toolchain.getToolchainXML();
		uploadFile(blobContainer, "toolchain", toolchainXML.getBytes());

		// Upload settingsFile to blob storage
		uploadFile(blobContainer, "settings", settingsFile.getBytes());

		// Upload settingsFile to blob storage
		uploadFile(blobContainer, "code", code.getBytes());

		addTaskToQueue(taskName);
	}

	private void addTaskToQueue(String text) {

		CloudQueue queue = initQueue();

		try {

			if (queue != null) {

				CloudQueueMessage message = new CloudQueueMessage(text);
				queue.addMessage(message);
			}

		} catch (StorageException e) {

		}
	}

	private CloudQueue initQueue() {
		try {

			CloudQueueClient client = account.createCloudQueueClient();
			CloudQueue queue = client.getQueueReference("tasks");
			queue.createIfNotExist();

			return queue;

		} catch (URISyntaxException e) {

		} catch (StorageException e) {

		}

		return null;
	}

	private CloudBlobContainer initBlob(String containerName) {
		try {

			CloudBlobClient client = account.createCloudBlobClient();
			CloudBlobContainer blobContainer;

			blobContainer = client.getContainerReference(containerName);
			blobContainer.createIfNotExist();

			return blobContainer;

		} catch (URISyntaxException e) {

		} catch (StorageException e) {

		}

		return null;
	}

	private void uploadFile(CloudBlobContainer blobContainer, String name,
			byte[] content) {

		if (name == null || name.isEmpty()) {
			throw new IllegalArgumentException("name");
		}

		if (blobContainer == null) {
			throw new IllegalArgumentException("blobContainer");
		}

		if (content == null || content.length == 0) {
			throw new IllegalArgumentException("content");
		}

		try {
			InputStream stream = new ByteArrayInputStream(content);
			CloudBlob blob;

			blob = blobContainer.getBlockBlobReference(name);
			blob.upload(stream, content.length);

		} catch (URISyntaxException e) {

		} catch (StorageException e) {

		} catch (IOException e) {

		}
	}
}
