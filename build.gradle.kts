import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    kotlin("jvm") version "1.7.10"
    application
}

group = "org.semgus.verifier"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
    maven("https://jitpack.io") { name = "Jitpack" }
}

dependencies {
    testImplementation(kotlin("test"))
    implementation("com.github.SemGuS-git:Semgus-Java:1.0.2")
    implementation("de.tu-dresden.inf.lat.jsexp:jsexp:0.2.2")
}

tasks.test {
    useJUnitPlatform()
}

tasks.withType<KotlinCompile> {
    kotlinOptions.jvmTarget = "1.8"
}

application {
    mainClass.set("MainKt")
}