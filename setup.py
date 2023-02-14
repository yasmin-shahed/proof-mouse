from importlib.metadata import entry_points
import setuptools

long_description = open('README.md').read()

setuptools.setup(
    name='pamplemousse',
    version='0.3',
    author='Raghav Malik',
    author_email='malik22@purdue.edu',
    description='Pamplemousse proof checker',
    long_description=long_description,
    url='https://github.com/raghav198/pamplemousse',
    license='MIT',
    packages=['.'],
    install_requires=['pyparsing==3.0.9'],
    entry_points={
        'console_scripts': ['mouse=pamplemousse:main']
    }
)
