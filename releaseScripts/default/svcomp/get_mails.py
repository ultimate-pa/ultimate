#!/usr/bin/env python3

import datetime
import getpass
from pathlib import Path
import ssl
from imap_tools import MailBox, AND, OR

ssl_context = ssl.create_default_context()
pwd = getpass.getpass(prompt="Password: ")
with MailBox("imap.informatik.uni-freiburg.de", ssl_context=ssl_context).login(
    "dietsch", pwd, "INBOX"
) as mailbox:
    date_format = "%Y%m%d_%H%M%S"
    since = datetime.date.today() - datetime.timedelta(days=7)
    limit = 10
    query = OR(
        *[AND(subject=s, date_gte=since) for s in ["Final Results", "Pre-run Results"]]
    )
    print(
        f"Getting last {limit} mails since {since.strftime(date_format)} with query '{query}'"
    )
    for msg in mailbox.fetch(
        query,
        limit=limit,
        reverse=True,
    ):
        filename = Path(f"{msg.date.strftime(date_format)}_{msg.subject}")
        if filename.is_file():
            print(f"Mail already there: '{msg.subject}' {msg.date_str}")
            continue
        print(f"Writing body of mail '{msg.subject}' {msg.date_str}")
        sanitized_subject = msg.subject.replace(" ", "_")
        with open(
            f"{msg.date.strftime(date_format)}_{sanitized_subject}.mail", "w"
        ) as f:
            f.write(msg.text)
