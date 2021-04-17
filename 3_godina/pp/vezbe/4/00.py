from PyQt5 import QtWidgets
from PyQt5.QtWidgets import QApplication, QMainWindow, QLabel

import sys

class MojProzor(QMainWindow):
    def __init__(self):
        super(MojProzor, self).__init__()
        self.initUI()

    def on_click(self):
        self.label.setText('kliknuto lolololol!!!')
        self.update()

    def update(self):
        self.label.adjustSize()

    def initUI(self):
        self.setGeometry(200, 200, 300, 300)
        self.setWindowTitle('Moj prozor')

        self.b1 = QtWidgets.QPushButton(self)
        self.b1.setText('klikni me')
        self.b1.move(100, 10)
        self.b1.clicked.connect(self.on_click)

        self.label= QLabel(self)
        self.label.setText('moja prva labela s')
        self.label.move(100, 50)


def main():
    app = QApplication(sys.argv)
    win = MojProzor()
    win.show()
    sys.exit(app.exec_())

main()

