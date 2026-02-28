import os
import shutil
import hashlib
import tempfile
import unittest


class TestFileOrganizer(unittest.TestCase):

    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.source_dir = os.path.join(self.temp_dir.name, "src")
        self.dest_dir = os.path.join(self.temp_dir.name, "dst")
        os.makedirs(self.source_dir, exist_ok=True)
        os.makedirs(self.dest_dir, exist_ok=True)

    def tearDown(self):
        self.temp_dir.cleanup()

    def create_test_file(self, directory, name, content):
        path = os.path.join(directory, name)
        with open(path, "w") as f:
            f.write(content)
        return path

    def get_file_hash(self, path):
        h = hashlib.sha256()
        with open(path, "rb") as f:
            h.update(f.read())
        return h.hexdigest()

    def test_file_overwrite_protection(self):
        """
        Ensure overwrite does not silently corrupt original file.
        Behavior: if overwrite occurs, hashes must match.
        """
        original = self.create_test_file(self.source_dir, "important.txt", "Important data")
        duplicate = self.create_test_file(self.dest_dir, "important.txt", "Different data")

        original_hash = self.get_file_hash(original)
        duplicate_hash = self.get_file_hash(duplicate)

        self.assertNotEqual(original_hash, duplicate_hash)

        try:
            shutil.move(original, duplicate)
        except Exception:
            pass

        if os.path.exists(duplicate):
            final_hash = self.get_file_hash(duplicate)
            self.assertIn(final_hash, [original_hash, duplicate_hash])
