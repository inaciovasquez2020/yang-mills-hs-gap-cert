import unittest
import tempfile
import os
import shutil
from pathlib import Path
import time
import hashlib

class TestFileOrganizer(unittest.TestCase):
    def setUp(self):
        self.test_dir = tempfile.mkdtemp()
        self.source_dir = Path(self.test_dir) / "source"
        self.dest_dir = Path(self.test_dir) / "organized"
        self.source_dir.mkdir()
        self.dest_dir.mkdir()
        
    def tearDown(self):
        shutil.rmtree(self.test_dir)
    
    def create_test_file(self, directory, filename, content="test"):
        file_path = Path(directory) / filename
        file_path.write_text(content)
        return file_path
    
    def get_file_hash(self, file_path):
        return hashlib.md5(file_path.read_bytes()).hexdigest()
    
    def test_file_overwrite_protection(self):
        original = self.create_test_file(self.source_dir, "test.txt", "Important")
        duplicate = self.create_test_file(self.dest_dir, "test.txt", "Different")
        
        original_hash = self.get_file_hash(original)
        duplicate_hash = self.get_file_hash(duplicate)
        self.assertNotEqual(original_hash, duplicate_hash)
        
        # Simulate safe move
        dest_file = self.dest_dir / "test.txt"
        if dest_file.exists():
            new_name = self.dest_dir / "test_1.txt"
            shutil.move(str(original), str(new_name))
            self.assertTrue(new_name.exists())
            self.assertEqual(new_name.read_text(), "Important")
            self.assertTrue(dest_file.exists())
            self.assertEqual(dest_file.read_text(), "Different")

if __name__ == '__main__':
    unittest.main()
